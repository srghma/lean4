// Lean compiler output
// Module: Std.Data.HashMap.Basic
// Imports: Std.Data.DHashMap.Basic Init.Data.List.Impl
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
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, l_List_foldrTR___redArg, runtime_initialize_Init_Data_List_Impl,
};
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
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
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
    l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg,
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
static mut l_Std_HashMap_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashMap_instEmptyCollection___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_instEmptyCollection___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashMap_term___x7em___00__closed__0_value: leanh::LeanStringObject<4> =
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
static mut l_Std_HashMap_term___x7em___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__1_value: leanh::LeanStringObject<8> =
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
static mut l_Std_HashMap_term___x7em___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__2_value: leanh::LeanStringObject<9> =
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
static mut l_Std_HashMap_term___x7em___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__2_value)
        as *mut leanh::LeanObject;
static l_Std_HashMap_term___x7em___00__closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_HashMap_term___x7em___00__closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__1_value)
                as *mut leanh::LeanObject,
            7102038059608022050 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_HashMap_term___x7em___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__2_value)
                as *mut leanh::LeanObject,
            10389554763822089420 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__4_value: leanh::LeanStringObject<8> =
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
static mut l_Std_HashMap_term___x7em___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__4_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__6_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_term___x7em___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Std_HashMap_term___x7em___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_term___x7em___00__closed__12_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__3_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_term___x7em___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_HashMap_term___x7em__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,6049842283740396800 as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap_term___x7em___00__closed__1_value) as *mut leanh::LeanObject,7102038059608022050 as *mut leanh::LeanObject] };
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value) as *mut leanh::LeanObject,11234608053757077773 as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_HashMap_keys___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_keys___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_keys___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_keys___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__10_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_keys___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keys___redArg___closed__11_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_keys___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_ofList___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_ofList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_ofList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_ofList___redArg___closed__1_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_ofList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_ofList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_ofList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_ofArray___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_ofArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_ofArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_ofArray___redArg___closed__1_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_ofArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_ofArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_ofArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_toList___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_toList___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_toList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_toList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_toArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_toArray___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_toArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_toArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_toArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_toArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keysArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_keysArray___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_keysArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keysArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_keysArray___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_keysArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_keysArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_keysArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_keysArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_all___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
static mut l_Std_HashMap_all___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_all___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_union___redArg___closed__0_value: leanh::LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_union___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_HashMap_partition___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_HashMap_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashMap_values___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_HashMap_values___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashMap_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_values___redArg___closed__1_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_HashMap_keys___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_HashMap_values___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_HashMap_values___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_values___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_valuesArray___redArg___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_valuesArray___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_HashMap_valuesArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_valuesArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_valuesArray___redArg___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_HashMap_keysArray___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_HashMap_keys___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_HashMap_valuesArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_valuesArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_valuesArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_HashMap_instRepr___redArg___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_HashMap_instRepr___redArg___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_HashMap_instRepr___redArg___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_HashMap_instRepr___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_groupByKey___redArg___lam__0___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Array_groupByKey___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_groupByKey___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_HashMap_emptyWithCapacity___redArg(
    mut v_capacity_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = leanh::lean_unsigned_to_nat(0);
    v___x_2261_ = leanh::lean_unsigned_to_nat(4);
    v___x_2262_ = lean_nat_mul(v_capacity_2259_, v___x_2261_);
    v___x_2263_ = leanh::lean_unsigned_to_nat(3);
    v___x_2264_ = lean_nat_div(v___x_2262_, v___x_2263_);
    leanh::lean_dec(v___x_2262_);
    v___x_2265_ = l_Nat_nextPowerOfTwo(v___x_2264_);
    leanh::lean_dec(v___x_2264_);
    v___x_2266_ = leanh::lean_box(0);
    v___x_2267_ = lean_mk_array(v___x_2265_, v___x_2266_);
    v___x_2268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2260_);
    leanh::lean_ctor_set(v___x_2268_, 1, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn l_Std_HashMap_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_Std_HashMap_emptyWithCapacity___redArg(v_capacity_2269_);
    leanh::lean_dec(v_capacity_2269_);
    return v_res_2270_;
}
pub unsafe fn l_Std_HashMap_emptyWithCapacity(
    mut v_00_u03b1_2271_: *mut leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_inst_2274_: *mut leanh::LeanObject,
    mut v_capacity_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = leanh::lean_unsigned_to_nat(0);
    v___x_2277_ = leanh::lean_unsigned_to_nat(4);
    v___x_2278_ = lean_nat_mul(v_capacity_2275_, v___x_2277_);
    v___x_2279_ = leanh::lean_unsigned_to_nat(3);
    v___x_2280_ = lean_nat_div(v___x_2278_, v___x_2279_);
    leanh::lean_dec(v___x_2278_);
    v___x_2281_ = l_Nat_nextPowerOfTwo(v___x_2280_);
    leanh::lean_dec(v___x_2280_);
    v___x_2282_ = leanh::lean_box(0);
    v___x_2283_ = lean_mk_array(v___x_2281_, v___x_2282_);
    v___x_2284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2284_, 0, v___x_2276_);
    leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
    return v___x_2284_;
}
pub unsafe fn l_Std_HashMap_emptyWithCapacity___boxed(
    mut v_00_u03b1_2285_: *mut leanh::LeanObject,
    mut v_00_u03b2_2286_: *mut leanh::LeanObject,
    mut v_inst_2287_: *mut leanh::LeanObject,
    mut v_inst_2288_: *mut leanh::LeanObject,
    mut v_capacity_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Std_HashMap_emptyWithCapacity(
        v_00_u03b1_2285_,
        v_00_u03b2_2286_,
        v_inst_2287_,
        v_inst_2288_,
        v_capacity_2289_,
    );
    leanh::lean_dec(v_capacity_2289_);
    leanh::lean_dec_ref(v_inst_2288_);
    leanh::lean_dec_ref(v_inst_2287_);
    return v_res_2290_;
}
pub unsafe fn _init_l_Std_HashMap_instEmptyCollection___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2291_ = leanh::lean_box(0);
    v___x_2292_ = leanh::lean_unsigned_to_nat(16);
    v___x_2293_ = lean_mk_array(v___x_2292_, v___x_2291_);
    return v___x_2293_;
}
pub unsafe fn _init_l_Std_HashMap_instEmptyCollection___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__0_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__0,
    );
    v___x_2295_ = leanh::lean_unsigned_to_nat(0);
    v___x_2296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2296_, 0, v___x_2295_);
    leanh::lean_ctor_set(v___x_2296_, 1, v___x_2294_);
    return v___x_2296_;
}
pub unsafe fn l_Std_HashMap_instEmptyCollection(
    mut v_00_u03b1_2297_: *mut leanh::LeanObject,
    mut v_00_u03b2_2298_: *mut leanh::LeanObject,
    mut v_inst_2299_: *mut leanh::LeanObject,
    mut v_inst_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    return v___x_2301_;
}
pub unsafe fn l_Std_HashMap_instEmptyCollection___boxed(
    mut v_00_u03b1_2302_: *mut leanh::LeanObject,
    mut v_00_u03b2_2303_: *mut leanh::LeanObject,
    mut v_inst_2304_: *mut leanh::LeanObject,
    mut v_inst_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2306_ = l_Std_HashMap_instEmptyCollection(
        v_00_u03b1_2302_,
        v_00_u03b2_2303_,
        v_inst_2304_,
        v_inst_2305_,
    );
    leanh::lean_dec_ref(v_inst_2305_);
    leanh::lean_dec_ref(v_inst_2304_);
    return v_res_2306_;
}
pub unsafe fn l_Std_HashMap_instInhabited(
    mut v_00_u03b1_2307_: *mut leanh::LeanObject,
    mut v_00_u03b2_2308_: *mut leanh::LeanObject,
    mut v_inst_2309_: *mut leanh::LeanObject,
    mut v_inst_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    return v___x_2311_;
}
pub unsafe fn l_Std_HashMap_instInhabited___boxed(
    mut v_00_u03b1_2312_: *mut leanh::LeanObject,
    mut v_00_u03b2_2313_: *mut leanh::LeanObject,
    mut v_inst_2314_: *mut leanh::LeanObject,
    mut v_inst_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2316_ = l_Std_HashMap_instInhabited(
        v_00_u03b1_2312_,
        v_00_u03b2_2313_,
        v_inst_2314_,
        v_inst_2315_,
    );
    leanh::lean_dec_ref(v_inst_2315_);
    leanh::lean_dec_ref(v_inst_2314_);
    return v_res_2316_;
}
pub unsafe fn _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5;
    v___x_2356_ = l_String_toRawSubstring_x27(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(
    mut v_x_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
    mut v_a_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    v___x_2380_ = l_Std_HashMap_term___x7em___00__closed__3;
    leanh::lean_inc(v_x_2377_);
    v___x_2381_ = l_Lean_Syntax_isOfKind(v_x_2377_, v___x_2380_);
    if v___x_2381_ == 0 {
        let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2377_);
        v___x_2382_ = leanh::lean_box(1);
        v___x_2383_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
        leanh::lean_ctor_set(v___x_2383_, 1, v_a_2379_);
        return v___x_2383_;
    } else {
        let mut v_quotContext_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: u8 = 0;
        let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2384_ = leanh::lean_ctor_get(v_a_2378_, 1);
        v_currMacroScope_2385_ = leanh::lean_ctor_get(v_a_2378_, 2);
        v_ref_2386_ = leanh::lean_ctor_get(v_a_2378_, 5);
        v___x_2387_ = leanh::lean_unsigned_to_nat(0);
        v___x_2388_ = l_Lean_Syntax_getArg(v_x_2377_, v___x_2387_);
        v___x_2389_ = leanh::lean_unsigned_to_nat(2);
        v___x_2390_ = l_Lean_Syntax_getArg(v_x_2377_, v___x_2389_);
        leanh::lean_dec(v_x_2377_);
        v___x_2391_ = 0;
        v___x_2392_ = l_Lean_SourceInfo_fromRef(v_ref_2386_, v___x_2391_);
        v___x_2393_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4;
        v___x_2394_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once), _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
        v___x_2395_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7;
        leanh::lean_inc(v_currMacroScope_2385_);
        leanh::lean_inc(v_quotContext_2384_);
        v___x_2396_ =
            l_Lean_addMacroScope(v_quotContext_2384_, v___x_2395_, v_currMacroScope_2385_);
        v___x_2397_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12;
        leanh::lean_inc_n(v___x_2392_, 2);
        v___x_2398_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2398_, 0, v___x_2392_);
        leanh::lean_ctor_set(v___x_2398_, 1, v___x_2394_);
        leanh::lean_ctor_set(v___x_2398_, 2, v___x_2396_);
        leanh::lean_ctor_set(v___x_2398_, 3, v___x_2397_);
        v___x_2399_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14;
        v___x_2400_ = l_Lean_Syntax_node2(v___x_2392_, v___x_2399_, v___x_2388_, v___x_2390_);
        v___x_2401_ = l_Lean_Syntax_node2(v___x_2392_, v___x_2393_, v___x_2398_, v___x_2400_);
        v___x_2402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2402_, 0, v___x_2401_);
        leanh::lean_ctor_set(v___x_2402_, 1, v_a_2379_);
        return v___x_2402_;
    }
}
pub unsafe fn l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(
    mut v_x_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
    mut v_a_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_2403_, v_a_2404_, v_a_2405_);
    leanh::lean_dec_ref(v_a_2404_);
    return v_res_2406_;
}
pub unsafe fn l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(
    mut v_x_2410_: *mut leanh::LeanObject,
    mut v_a_2411_: *mut leanh::LeanObject,
    mut v_a_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: u8 = 0;
    v___x_2413_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4;
    leanh::lean_inc(v_x_2410_);
    v___x_2414_ = l_Lean_Syntax_isOfKind(v_x_2410_, v___x_2413_);
    if v___x_2414_ == 0 {
        let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2410_);
        v___x_2415_ = leanh::lean_box(0);
        v___x_2416_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2416_, 0, v___x_2415_);
        leanh::lean_ctor_set(v___x_2416_, 1, v_a_2412_);
        return v___x_2416_;
    } else {
        let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: u8 = 0;
        v___x_2417_ = leanh::lean_unsigned_to_nat(0);
        v___x_2418_ = l_Lean_Syntax_getArg(v_x_2410_, v___x_2417_);
        v___x_2419_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1;
        leanh::lean_inc(v___x_2418_);
        v___x_2420_ = l_Lean_Syntax_isOfKind(v___x_2418_, v___x_2419_);
        if v___x_2420_ == 0 {
            let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2418_);
            leanh::lean_dec(v_x_2410_);
            v___x_2421_ = leanh::lean_box(0);
            v___x_2422_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2422_, 0, v___x_2421_);
            leanh::lean_ctor_set(v___x_2422_, 1, v_a_2412_);
            return v___x_2422_;
        } else {
            let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2426_: u8 = 0;
            v___x_2423_ = leanh::lean_unsigned_to_nat(1);
            v___x_2424_ = l_Lean_Syntax_getArg(v_x_2410_, v___x_2423_);
            leanh::lean_dec(v_x_2410_);
            v___x_2425_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2424_);
            v___x_2426_ = l_Lean_Syntax_matchesNull(v___x_2424_, v___x_2425_);
            if v___x_2426_ == 0 {
                let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2424_);
                leanh::lean_dec(v___x_2418_);
                v___x_2427_ = leanh::lean_box(0);
                v___x_2428_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2428_, 0, v___x_2427_);
                leanh::lean_ctor_set(v___x_2428_, 1, v_a_2412_);
                return v___x_2428_;
            } else {
                let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2432_: u8 = 0;
                let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2429_ = l_Lean_Syntax_getArg(v___x_2424_, v___x_2417_);
                v___x_2430_ = l_Lean_Syntax_getArg(v___x_2424_, v___x_2423_);
                leanh::lean_dec(v___x_2424_);
                v_ref_2431_ = l_Lean_replaceRef(v___x_2418_, v_a_2411_);
                leanh::lean_dec(v___x_2418_);
                v___x_2432_ = 0;
                v___x_2433_ = l_Lean_SourceInfo_fromRef(v_ref_2431_, v___x_2432_);
                leanh::lean_dec(v_ref_2431_);
                v___x_2434_ = l_Std_HashMap_term___x7em___00__closed__3;
                v___x_2435_ = l_Std_HashMap_term___x7em___00__closed__6;
                leanh::lean_inc(v___x_2433_);
                v___x_2436_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2436_, 0, v___x_2433_);
                leanh::lean_ctor_set(v___x_2436_, 1, v___x_2435_);
                v___x_2437_ = l_Lean_Syntax_node3(
                    v___x_2433_,
                    v___x_2434_,
                    v___x_2429_,
                    v___x_2436_,
                    v___x_2430_,
                );
                v___x_2438_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2438_, 0, v___x_2437_);
                leanh::lean_ctor_set(v___x_2438_, 1, v_a_2412_);
                return v___x_2438_;
            }
        }
    }
}
pub unsafe fn l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(
    mut v_x_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2442_ =
        l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(
            v_x_2439_, v_a_2440_, v_a_2441_,
        );
    leanh::lean_dec(v_a_2440_);
    return v_res_2442_;
}
pub unsafe fn l_Std_HashMap_insert___redArg(
    mut v_x_2443_: *mut leanh::LeanObject,
    mut v_x_2444_: *mut leanh::LeanObject,
    mut v_m_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_b_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2443_, v_x_2444_, v_m_2445_, v_a_2446_, v_b_2447_,
    );
    return v___x_2448_;
}
pub unsafe fn l_Std_HashMap_insert(
    mut v_00_u03b1_2449_: *mut leanh::LeanObject,
    mut v_00_u03b2_2450_: *mut leanh::LeanObject,
    mut v_x_2451_: *mut leanh::LeanObject,
    mut v_x_2452_: *mut leanh::LeanObject,
    mut v_m_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_b_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2451_, v_x_2452_, v_m_2453_, v_a_2454_, v_b_2455_,
    );
    return v___x_2456_;
}
pub unsafe fn l_Std_HashMap_instSingletonProd___redArg___lam__0(
    mut v_x_2457_: *mut leanh::LeanObject,
    mut v_x_2458_: *mut leanh::LeanObject,
    mut v_x_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2460_ = leanh::lean_ctor_get(v_x_2459_, 0);
    leanh::lean_inc(v_fst_2460_);
    v_snd_2461_ = leanh::lean_ctor_get(v_x_2459_, 1);
    leanh::lean_inc(v_snd_2461_);
    leanh::lean_dec_ref(v_x_2459_);
    v___x_2462_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2457_,
        v_x_2458_,
        v___x_2462_,
        v_fst_2460_,
        v_snd_2461_,
    );
    return v___x_2463_;
}
pub unsafe fn l_Std_HashMap_instSingletonProd___redArg(
    mut v_x_2464_: *mut leanh::LeanObject,
    mut v_x_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2466_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2466_, 0, v_x_2464_);
    leanh::lean_closure_set(v___f_2466_, 1, v_x_2465_);
    return v___f_2466_;
}
pub unsafe fn l_Std_HashMap_instSingletonProd(
    mut v_00_u03b1_2467_: *mut leanh::LeanObject,
    mut v_00_u03b2_2468_: *mut leanh::LeanObject,
    mut v_x_2469_: *mut leanh::LeanObject,
    mut v_x_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2471_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instSingletonProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2471_, 0, v_x_2469_);
    leanh::lean_closure_set(v___f_2471_, 1, v_x_2470_);
    return v___f_2471_;
}
pub unsafe fn l_Std_HashMap_instInsertProd___redArg___lam__0(
    mut v_x_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: *mut leanh::LeanObject,
    mut v_x_2474_: *mut leanh::LeanObject,
    mut v_s_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2476_ = leanh::lean_ctor_get(v_x_2474_, 0);
    leanh::lean_inc(v_fst_2476_);
    v_snd_2477_ = leanh::lean_ctor_get(v_x_2474_, 1);
    leanh::lean_inc(v_snd_2477_);
    leanh::lean_dec_ref(v_x_2474_);
    v___x_2478_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_x_2472_,
        v_x_2473_,
        v_s_2475_,
        v_fst_2476_,
        v_snd_2477_,
    );
    return v___x_2478_;
}
pub unsafe fn l_Std_HashMap_instInsertProd___redArg(
    mut v_x_2479_: *mut leanh::LeanObject,
    mut v_x_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2481_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2481_, 0, v_x_2479_);
    leanh::lean_closure_set(v___f_2481_, 1, v_x_2480_);
    return v___f_2481_;
}
pub unsafe fn l_Std_HashMap_instInsertProd(
    mut v_00_u03b1_2482_: *mut leanh::LeanObject,
    mut v_00_u03b2_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
    mut v_x_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2486_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instInsertProd___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2486_, 0, v_x_2484_);
    leanh::lean_closure_set(v___f_2486_, 1, v_x_2485_);
    return v___f_2486_;
}
pub unsafe fn l_Std_HashMap_insertIfNew___redArg(
    mut v_x_2487_: *mut leanh::LeanObject,
    mut v_x_2488_: *mut leanh::LeanObject,
    mut v_m_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_b_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2487_, v_x_2488_, v_m_2489_, v_a_2490_, v_b_2491_,
    );
    return v___x_2492_;
}
pub unsafe fn l_Std_HashMap_insertIfNew(
    mut v_00_u03b1_2493_: *mut leanh::LeanObject,
    mut v_00_u03b2_2494_: *mut leanh::LeanObject,
    mut v_x_2495_: *mut leanh::LeanObject,
    mut v_x_2496_: *mut leanh::LeanObject,
    mut v_m_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_b_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2500_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_2495_, v_x_2496_, v_m_2497_, v_a_2498_, v_b_2499_,
    );
    return v___x_2500_;
}
pub unsafe fn l_Std_HashMap_containsThenInsert___redArg(
    mut v_x_2501_: *mut leanh::LeanObject,
    mut v_x_2502_: *mut leanh::LeanObject,
    mut v_m_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
    mut v_b_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u64 = 0;
    let mut v___x_2514_: u64 = 0;
    let mut v___x_2515_: u64 = 0;
    let mut v___x_2516_: u64 = 0;
    let mut v_fold_2517_: u64 = 0;
    let mut v___x_2518_: u64 = 0;
    let mut v___x_2519_: u64 = 0;
    let mut v___x_2520_: u64 = 0;
    let mut v___x_2521_: usize = 0;
    let mut v___x_2522_: usize = 0;
    let mut v___x_2523_: usize = 0;
    let mut v___x_2524_: usize = 0;
    let mut v___x_2525_: usize = 0;
    let mut v_bkt_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v_val_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2506_ = leanh::lean_ctor_get(v_m_2503_, 0);
                v_buckets_2507_ = leanh::lean_ctor_get(v_m_2503_, 1);
                v_isSharedCheck_2558_ = (!leanh::lean_is_exclusive(v_m_2503_)) as u8;
                if v_isSharedCheck_2558_ == 0 {
                    v___x_2509_ = v_m_2503_;
                    v_isShared_2510_ = v_isSharedCheck_2558_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2507_);
                    leanh::lean_inc(v_size_2506_);
                    leanh::lean_dec(v_m_2503_);
                    v___x_2509_ = leanh::lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2558_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2511_ = lean_array_get_size(v_buckets_2507_);
                leanh::lean_inc_ref(v_x_2502_);
                leanh::lean_inc_n(v_a_2504_, 2);
                v___x_2512_ = leanh::lean_apply_1(v_x_2502_, v_a_2504_);
                v___x_2513_ = 32u64;
                v___x_2514_ = leanh::lean_unbox_uint64(v___x_2512_);
                v___x_2515_ = lean_uint64_shift_right(v___x_2514_, v___x_2513_);
                v___x_2516_ = leanh::lean_unbox_uint64(v___x_2512_);
                leanh::lean_dec_ref(v___x_2512_);
                v_fold_2517_ = lean_uint64_xor(v___x_2516_, v___x_2515_);
                v___x_2518_ = 16u64;
                v___x_2519_ = lean_uint64_shift_right(v_fold_2517_, v___x_2518_);
                v___x_2520_ = lean_uint64_xor(v_fold_2517_, v___x_2519_);
                v___x_2521_ = lean_uint64_to_usize(v___x_2520_);
                v___x_2522_ = lean_usize_of_nat(v___x_2511_);
                v___x_2523_ = 1usize;
                v___x_2524_ = lean_usize_sub(v___x_2522_, v___x_2523_);
                v___x_2525_ = lean_usize_land(v___x_2521_, v___x_2524_);
                v_bkt_2526_ = lean_array_uget_borrowed(v_buckets_2507_, v___x_2525_);
                leanh::lean_inc(v_bkt_2526_);
                leanh::lean_inc_ref(v_x_2501_);
                v___x_2527_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2501_,
                    v_a_2504_,
                    v_bkt_2526_,
                );
                if v___x_2527_ == 0 {
                    leanh::lean_dec_ref(v_x_2501_);
                    v___x_2528_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2529_ = lean_nat_add(v_size_2506_, v___x_2528_);
                    leanh::lean_dec(v_size_2506_);
                    leanh::lean_inc(v_bkt_2526_);
                    v___x_2530_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2530_, 0, v_a_2504_);
                    leanh::lean_ctor_set(v___x_2530_, 1, v_b_2505_);
                    leanh::lean_ctor_set(v___x_2530_, 2, v_bkt_2526_);
                    v_buckets_x27_2531_ =
                        lean_array_uset(v_buckets_2507_, v___x_2525_, v___x_2530_);
                    v___x_2532_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2533_ = lean_nat_mul(v_size_x27_2529_, v___x_2532_);
                    v___x_2534_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2535_ = lean_nat_div(v___x_2533_, v___x_2534_);
                    leanh::lean_dec(v___x_2533_);
                    v___x_2536_ = lean_array_get_size(v_buckets_x27_2531_);
                    v___x_2537_ = lean_nat_dec_le(v___x_2535_, v___x_2536_);
                    leanh::lean_dec(v___x_2535_);
                    if v___x_2537_ == 0 {
                        v_val_2538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_2502_,
                            v_buckets_x27_2531_,
                        );
                        if v_isShared_2510_ == 0 {
                            leanh::lean_ctor_set(v___x_2509_, 1, v_val_2538_);
                            leanh::lean_ctor_set(v___x_2509_, 0, v_size_x27_2529_);
                            v___x_2540_ = v___x_2509_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2543_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2543_,
                                0,
                                v_size_x27_2529_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_val_2538_);
                            v___x_2540_ = v_reuseFailAlloc_2543_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_2502_);
                        if v_isShared_2510_ == 0 {
                            leanh::lean_ctor_set(v___x_2509_, 1, v_buckets_x27_2531_);
                            leanh::lean_ctor_set(v___x_2509_, 0, v_size_x27_2529_);
                            v___x_2545_ = v___x_2509_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2548_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2548_,
                                0,
                                v_size_x27_2529_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2548_,
                                1,
                                v_buckets_x27_2531_,
                            );
                            v___x_2545_ = v_reuseFailAlloc_2548_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2526_);
                    leanh::lean_dec_ref(v_x_2502_);
                    v___x_2549_ = leanh::lean_box(0);
                    v_buckets_x27_2550_ =
                        lean_array_uset(v_buckets_2507_, v___x_2525_, v___x_2549_);
                    v___x_2551_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_2501_,
                        v_a_2504_,
                        v_b_2505_,
                        v_bkt_2526_,
                    );
                    v___x_2552_ = lean_array_uset(v_buckets_x27_2550_, v___x_2525_, v___x_2551_);
                    if v_isShared_2510_ == 0 {
                        leanh::lean_ctor_set(v___x_2509_, 1, v___x_2552_);
                        v___x_2554_ = v___x_2509_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2557_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_2506_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2552_);
                        v___x_2554_ = v_reuseFailAlloc_2557_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2541_ = leanh::lean_box((v___x_2527_) as usize);
                v___x_2542_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
                leanh::lean_ctor_set(v___x_2542_, 1, v___x_2540_);
                return v___x_2542_;
            }
            3 => {
                v___x_2546_ = leanh::lean_box((v___x_2527_) as usize);
                v___x_2547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2547_, 0, v___x_2546_);
                leanh::lean_ctor_set(v___x_2547_, 1, v___x_2545_);
                return v___x_2547_;
            }
            4 => {
                v___x_2555_ = leanh::lean_box((v___x_2527_) as usize);
                v___x_2556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2556_, 0, v___x_2555_);
                leanh::lean_ctor_set(v___x_2556_, 1, v___x_2554_);
                return v___x_2556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_containsThenInsert(
    mut v_00_u03b1_2559_: *mut leanh::LeanObject,
    mut v_00_u03b2_2560_: *mut leanh::LeanObject,
    mut v_x_2561_: *mut leanh::LeanObject,
    mut v_x_2562_: *mut leanh::LeanObject,
    mut v_m_2563_: *mut leanh::LeanObject,
    mut v_a_2564_: *mut leanh::LeanObject,
    mut v_b_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u64 = 0;
    let mut v___x_2574_: u64 = 0;
    let mut v___x_2575_: u64 = 0;
    let mut v___x_2576_: u64 = 0;
    let mut v_fold_2577_: u64 = 0;
    let mut v___x_2578_: u64 = 0;
    let mut v___x_2579_: u64 = 0;
    let mut v___x_2580_: u64 = 0;
    let mut v___x_2581_: usize = 0;
    let mut v___x_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: usize = 0;
    let mut v_bkt_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v_val_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2566_ = leanh::lean_ctor_get(v_m_2563_, 0);
                v_buckets_2567_ = leanh::lean_ctor_get(v_m_2563_, 1);
                v_isSharedCheck_2618_ = (!leanh::lean_is_exclusive(v_m_2563_)) as u8;
                if v_isSharedCheck_2618_ == 0 {
                    v___x_2569_ = v_m_2563_;
                    v_isShared_2570_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2567_);
                    leanh::lean_inc(v_size_2566_);
                    leanh::lean_dec(v_m_2563_);
                    v___x_2569_ = leanh::lean_box(0);
                    v_isShared_2570_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2571_ = lean_array_get_size(v_buckets_2567_);
                leanh::lean_inc_ref(v_x_2562_);
                leanh::lean_inc_n(v_a_2564_, 2);
                v___x_2572_ = leanh::lean_apply_1(v_x_2562_, v_a_2564_);
                v___x_2573_ = 32u64;
                v___x_2574_ = leanh::lean_unbox_uint64(v___x_2572_);
                v___x_2575_ = lean_uint64_shift_right(v___x_2574_, v___x_2573_);
                v___x_2576_ = leanh::lean_unbox_uint64(v___x_2572_);
                leanh::lean_dec_ref(v___x_2572_);
                v_fold_2577_ = lean_uint64_xor(v___x_2576_, v___x_2575_);
                v___x_2578_ = 16u64;
                v___x_2579_ = lean_uint64_shift_right(v_fold_2577_, v___x_2578_);
                v___x_2580_ = lean_uint64_xor(v_fold_2577_, v___x_2579_);
                v___x_2581_ = lean_uint64_to_usize(v___x_2580_);
                v___x_2582_ = lean_usize_of_nat(v___x_2571_);
                v___x_2583_ = 1usize;
                v___x_2584_ = lean_usize_sub(v___x_2582_, v___x_2583_);
                v___x_2585_ = lean_usize_land(v___x_2581_, v___x_2584_);
                v_bkt_2586_ = lean_array_uget_borrowed(v_buckets_2567_, v___x_2585_);
                leanh::lean_inc(v_bkt_2586_);
                leanh::lean_inc_ref(v_x_2561_);
                v___x_2587_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2561_,
                    v_a_2564_,
                    v_bkt_2586_,
                );
                if v___x_2587_ == 0 {
                    leanh::lean_dec_ref(v_x_2561_);
                    v___x_2588_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2589_ = lean_nat_add(v_size_2566_, v___x_2588_);
                    leanh::lean_dec(v_size_2566_);
                    leanh::lean_inc(v_bkt_2586_);
                    v___x_2590_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2590_, 0, v_a_2564_);
                    leanh::lean_ctor_set(v___x_2590_, 1, v_b_2565_);
                    leanh::lean_ctor_set(v___x_2590_, 2, v_bkt_2586_);
                    v_buckets_x27_2591_ =
                        lean_array_uset(v_buckets_2567_, v___x_2585_, v___x_2590_);
                    v___x_2592_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2593_ = lean_nat_mul(v_size_x27_2589_, v___x_2592_);
                    v___x_2594_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2595_ = lean_nat_div(v___x_2593_, v___x_2594_);
                    leanh::lean_dec(v___x_2593_);
                    v___x_2596_ = lean_array_get_size(v_buckets_x27_2591_);
                    v___x_2597_ = lean_nat_dec_le(v___x_2595_, v___x_2596_);
                    leanh::lean_dec(v___x_2595_);
                    if v___x_2597_ == 0 {
                        v_val_2598_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_x_2562_,
                            v_buckets_x27_2591_,
                        );
                        if v_isShared_2570_ == 0 {
                            leanh::lean_ctor_set(v___x_2569_, 1, v_val_2598_);
                            leanh::lean_ctor_set(v___x_2569_, 0, v_size_x27_2589_);
                            v___x_2600_ = v___x_2569_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2603_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2603_,
                                0,
                                v_size_x27_2589_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_val_2598_);
                            v___x_2600_ = v_reuseFailAlloc_2603_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_2562_);
                        if v_isShared_2570_ == 0 {
                            leanh::lean_ctor_set(v___x_2569_, 1, v_buckets_x27_2591_);
                            leanh::lean_ctor_set(v___x_2569_, 0, v_size_x27_2589_);
                            v___x_2605_ = v___x_2569_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2608_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2608_,
                                0,
                                v_size_x27_2589_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2608_,
                                1,
                                v_buckets_x27_2591_,
                            );
                            v___x_2605_ = v_reuseFailAlloc_2608_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2586_);
                    leanh::lean_dec_ref(v_x_2562_);
                    v___x_2609_ = leanh::lean_box(0);
                    v_buckets_x27_2610_ =
                        lean_array_uset(v_buckets_2567_, v___x_2585_, v___x_2609_);
                    v___x_2611_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_x_2561_,
                        v_a_2564_,
                        v_b_2565_,
                        v_bkt_2586_,
                    );
                    v___x_2612_ = lean_array_uset(v_buckets_x27_2610_, v___x_2585_, v___x_2611_);
                    if v_isShared_2570_ == 0 {
                        leanh::lean_ctor_set(v___x_2569_, 1, v___x_2612_);
                        v___x_2614_ = v___x_2569_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_size_2566_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2612_);
                        v___x_2614_ = v_reuseFailAlloc_2617_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2601_ = leanh::lean_box((v___x_2587_) as usize);
                v___x_2602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2602_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2602_, 1, v___x_2600_);
                return v___x_2602_;
            }
            3 => {
                v___x_2606_ = leanh::lean_box((v___x_2587_) as usize);
                v___x_2607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2607_, 0, v___x_2606_);
                leanh::lean_ctor_set(v___x_2607_, 1, v___x_2605_);
                return v___x_2607_;
            }
            4 => {
                v___x_2615_ = leanh::lean_box((v___x_2587_) as usize);
                v___x_2616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2616_, 0, v___x_2615_);
                leanh::lean_ctor_set(v___x_2616_, 1, v___x_2614_);
                return v___x_2616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_containsThenInsertIfNew___redArg(
    mut v_x_2619_: *mut leanh::LeanObject,
    mut v_x_2620_: *mut leanh::LeanObject,
    mut v_m_2621_: *mut leanh::LeanObject,
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_b_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u64 = 0;
    let mut v___x_2629_: u64 = 0;
    let mut v___x_2630_: u64 = 0;
    let mut v___x_2631_: u64 = 0;
    let mut v_fold_2632_: u64 = 0;
    let mut v___x_2633_: u64 = 0;
    let mut v___x_2634_: u64 = 0;
    let mut v___x_2635_: u64 = 0;
    let mut v___x_2636_: usize = 0;
    let mut v___x_2637_: usize = 0;
    let mut v___x_2638_: usize = 0;
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v_bkt_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2645_: u8 = 0;
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: u8 = 0;
    let mut v_val_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_unused_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2624_ = leanh::lean_ctor_get(v_m_2621_, 0);
                v_buckets_2625_ = leanh::lean_ctor_get(v_m_2621_, 1);
                v___x_2626_ = lean_array_get_size(v_buckets_2625_);
                leanh::lean_inc_ref(v_x_2620_);
                leanh::lean_inc_n(v_a_2622_, 2);
                v___x_2627_ = leanh::lean_apply_1(v_x_2620_, v_a_2622_);
                v___x_2628_ = 32u64;
                v___x_2629_ = leanh::lean_unbox_uint64(v___x_2627_);
                v___x_2630_ = lean_uint64_shift_right(v___x_2629_, v___x_2628_);
                v___x_2631_ = leanh::lean_unbox_uint64(v___x_2627_);
                leanh::lean_dec_ref(v___x_2627_);
                v_fold_2632_ = lean_uint64_xor(v___x_2631_, v___x_2630_);
                v___x_2633_ = 16u64;
                v___x_2634_ = lean_uint64_shift_right(v_fold_2632_, v___x_2633_);
                v___x_2635_ = lean_uint64_xor(v_fold_2632_, v___x_2634_);
                v___x_2636_ = lean_uint64_to_usize(v___x_2635_);
                v___x_2637_ = lean_usize_of_nat(v___x_2626_);
                v___x_2638_ = 1usize;
                v___x_2639_ = lean_usize_sub(v___x_2637_, v___x_2638_);
                v___x_2640_ = lean_usize_land(v___x_2636_, v___x_2639_);
                v_bkt_2641_ = lean_array_uget_borrowed(v_buckets_2625_, v___x_2640_);
                leanh::lean_inc(v_bkt_2641_);
                v___x_2642_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2619_,
                    v_a_2622_,
                    v_bkt_2641_,
                );
                if v___x_2642_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2625_);
                    leanh::lean_inc(v_size_2624_);
                    v_isSharedCheck_2667_ = (!leanh::lean_is_exclusive(v_m_2621_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v_unused_2668_ = leanh::lean_ctor_get(v_m_2621_, 1);
                        leanh::lean_dec(v_unused_2668_);
                        v_unused_2669_ = leanh::lean_ctor_get(v_m_2621_, 0);
                        leanh::lean_dec(v_unused_2669_);
                        v___x_2644_ = v_m_2621_;
                        v_isShared_2645_ = v_isSharedCheck_2667_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2621_);
                        v___x_2644_ = leanh::lean_box(0);
                        v_isShared_2645_ = v_isSharedCheck_2667_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2623_);
                    leanh::lean_dec(v_a_2622_);
                    leanh::lean_dec_ref(v_x_2620_);
                    v___x_2670_ = leanh::lean_box((v___x_2642_) as usize);
                    v___x_2671_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2671_, 0, v___x_2670_);
                    leanh::lean_ctor_set(v___x_2671_, 1, v_m_2621_);
                    return v___x_2671_;
                }
            }
            1 => {
                v___x_2646_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2647_ = lean_nat_add(v_size_2624_, v___x_2646_);
                leanh::lean_dec(v_size_2624_);
                leanh::lean_inc(v_bkt_2641_);
                v___x_2648_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2648_, 0, v_a_2622_);
                leanh::lean_ctor_set(v___x_2648_, 1, v_b_2623_);
                leanh::lean_ctor_set(v___x_2648_, 2, v_bkt_2641_);
                v_buckets_x27_2649_ = lean_array_uset(v_buckets_2625_, v___x_2640_, v___x_2648_);
                v___x_2650_ = leanh::lean_unsigned_to_nat(4);
                v___x_2651_ = lean_nat_mul(v_size_x27_2647_, v___x_2650_);
                v___x_2652_ = leanh::lean_unsigned_to_nat(3);
                v___x_2653_ = lean_nat_div(v___x_2651_, v___x_2652_);
                leanh::lean_dec(v___x_2651_);
                v___x_2654_ = lean_array_get_size(v_buckets_x27_2649_);
                v___x_2655_ = lean_nat_dec_le(v___x_2653_, v___x_2654_);
                leanh::lean_dec(v___x_2653_);
                if v___x_2655_ == 0 {
                    v_val_2656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2620_,
                        v_buckets_x27_2649_,
                    );
                    if v_isShared_2645_ == 0 {
                        leanh::lean_ctor_set(v___x_2644_, 1, v_val_2656_);
                        leanh::lean_ctor_set(v___x_2644_, 0, v_size_x27_2647_);
                        v___x_2658_ = v___x_2644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2661_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_size_x27_2647_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_val_2656_);
                        v___x_2658_ = v_reuseFailAlloc_2661_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2620_);
                    if v_isShared_2645_ == 0 {
                        leanh::lean_ctor_set(v___x_2644_, 1, v_buckets_x27_2649_);
                        leanh::lean_ctor_set(v___x_2644_, 0, v_size_x27_2647_);
                        v___x_2663_ = v___x_2644_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2666_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_size_x27_2647_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_buckets_x27_2649_);
                        v___x_2663_ = v_reuseFailAlloc_2666_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2659_ = leanh::lean_box((v___x_2642_) as usize);
                v___x_2660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2660_, 0, v___x_2659_);
                leanh::lean_ctor_set(v___x_2660_, 1, v___x_2658_);
                return v___x_2660_;
            }
            3 => {
                v___x_2664_ = leanh::lean_box((v___x_2642_) as usize);
                v___x_2665_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2665_, 0, v___x_2664_);
                leanh::lean_ctor_set(v___x_2665_, 1, v___x_2663_);
                return v___x_2665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_containsThenInsertIfNew(
    mut v_00_u03b1_2672_: *mut leanh::LeanObject,
    mut v_00_u03b2_2673_: *mut leanh::LeanObject,
    mut v_x_2674_: *mut leanh::LeanObject,
    mut v_x_2675_: *mut leanh::LeanObject,
    mut v_m_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_b_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    let mut v___x_2685_: u64 = 0;
    let mut v___x_2686_: u64 = 0;
    let mut v_fold_2687_: u64 = 0;
    let mut v___x_2688_: u64 = 0;
    let mut v___x_2689_: u64 = 0;
    let mut v___x_2690_: u64 = 0;
    let mut v___x_2691_: usize = 0;
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: usize = 0;
    let mut v___x_2695_: usize = 0;
    let mut v_bkt_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: u8 = 0;
    let mut v_val_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut v_unused_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2679_ = leanh::lean_ctor_get(v_m_2676_, 0);
                v_buckets_2680_ = leanh::lean_ctor_get(v_m_2676_, 1);
                v___x_2681_ = lean_array_get_size(v_buckets_2680_);
                leanh::lean_inc_ref(v_x_2675_);
                leanh::lean_inc_n(v_a_2677_, 2);
                v___x_2682_ = leanh::lean_apply_1(v_x_2675_, v_a_2677_);
                v___x_2683_ = 32u64;
                v___x_2684_ = leanh::lean_unbox_uint64(v___x_2682_);
                v___x_2685_ = lean_uint64_shift_right(v___x_2684_, v___x_2683_);
                v___x_2686_ = leanh::lean_unbox_uint64(v___x_2682_);
                leanh::lean_dec_ref(v___x_2682_);
                v_fold_2687_ = lean_uint64_xor(v___x_2686_, v___x_2685_);
                v___x_2688_ = 16u64;
                v___x_2689_ = lean_uint64_shift_right(v_fold_2687_, v___x_2688_);
                v___x_2690_ = lean_uint64_xor(v_fold_2687_, v___x_2689_);
                v___x_2691_ = lean_uint64_to_usize(v___x_2690_);
                v___x_2692_ = lean_usize_of_nat(v___x_2681_);
                v___x_2693_ = 1usize;
                v___x_2694_ = lean_usize_sub(v___x_2692_, v___x_2693_);
                v___x_2695_ = lean_usize_land(v___x_2691_, v___x_2694_);
                v_bkt_2696_ = lean_array_uget_borrowed(v_buckets_2680_, v___x_2695_);
                leanh::lean_inc(v_bkt_2696_);
                v___x_2697_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_2674_,
                    v_a_2677_,
                    v_bkt_2696_,
                );
                if v___x_2697_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2680_);
                    leanh::lean_inc(v_size_2679_);
                    v_isSharedCheck_2722_ = (!leanh::lean_is_exclusive(v_m_2676_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v_unused_2723_ = leanh::lean_ctor_get(v_m_2676_, 1);
                        leanh::lean_dec(v_unused_2723_);
                        v_unused_2724_ = leanh::lean_ctor_get(v_m_2676_, 0);
                        leanh::lean_dec(v_unused_2724_);
                        v___x_2699_ = v_m_2676_;
                        v_isShared_2700_ = v_isSharedCheck_2722_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2676_);
                        v___x_2699_ = leanh::lean_box(0);
                        v_isShared_2700_ = v_isSharedCheck_2722_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2678_);
                    leanh::lean_dec(v_a_2677_);
                    leanh::lean_dec_ref(v_x_2675_);
                    v___x_2725_ = leanh::lean_box((v___x_2697_) as usize);
                    v___x_2726_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2726_, 0, v___x_2725_);
                    leanh::lean_ctor_set(v___x_2726_, 1, v_m_2676_);
                    return v___x_2726_;
                }
            }
            1 => {
                v___x_2701_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2702_ = lean_nat_add(v_size_2679_, v___x_2701_);
                leanh::lean_dec(v_size_2679_);
                leanh::lean_inc(v_bkt_2696_);
                v___x_2703_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2703_, 0, v_a_2677_);
                leanh::lean_ctor_set(v___x_2703_, 1, v_b_2678_);
                leanh::lean_ctor_set(v___x_2703_, 2, v_bkt_2696_);
                v_buckets_x27_2704_ = lean_array_uset(v_buckets_2680_, v___x_2695_, v___x_2703_);
                v___x_2705_ = leanh::lean_unsigned_to_nat(4);
                v___x_2706_ = lean_nat_mul(v_size_x27_2702_, v___x_2705_);
                v___x_2707_ = leanh::lean_unsigned_to_nat(3);
                v___x_2708_ = lean_nat_div(v___x_2706_, v___x_2707_);
                leanh::lean_dec(v___x_2706_);
                v___x_2709_ = lean_array_get_size(v_buckets_x27_2704_);
                v___x_2710_ = lean_nat_dec_le(v___x_2708_, v___x_2709_);
                leanh::lean_dec(v___x_2708_);
                if v___x_2710_ == 0 {
                    v_val_2711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2675_,
                        v_buckets_x27_2704_,
                    );
                    if v_isShared_2700_ == 0 {
                        leanh::lean_ctor_set(v___x_2699_, 1, v_val_2711_);
                        leanh::lean_ctor_set(v___x_2699_, 0, v_size_x27_2702_);
                        v___x_2713_ = v___x_2699_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_size_x27_2702_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_val_2711_);
                        v___x_2713_ = v_reuseFailAlloc_2716_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2675_);
                    if v_isShared_2700_ == 0 {
                        leanh::lean_ctor_set(v___x_2699_, 1, v_buckets_x27_2704_);
                        leanh::lean_ctor_set(v___x_2699_, 0, v_size_x27_2702_);
                        v___x_2718_ = v___x_2699_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2721_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_size_x27_2702_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_buckets_x27_2704_);
                        v___x_2718_ = v_reuseFailAlloc_2721_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2714_ = leanh::lean_box((v___x_2697_) as usize);
                v___x_2715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2715_, 0, v___x_2714_);
                leanh::lean_ctor_set(v___x_2715_, 1, v___x_2713_);
                return v___x_2715_;
            }
            3 => {
                v___x_2719_ = leanh::lean_box((v___x_2697_) as usize);
                v___x_2720_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2720_, 0, v___x_2719_);
                leanh::lean_ctor_set(v___x_2720_, 1, v___x_2718_);
                return v___x_2720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_getThenInsertIfNew_x3f___redArg(
    mut v_x_2727_: *mut leanh::LeanObject,
    mut v_x_2728_: *mut leanh::LeanObject,
    mut v_m_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_b_2731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: u64 = 0;
    let mut v___x_2737_: u64 = 0;
    let mut v___x_2738_: u64 = 0;
    let mut v___x_2739_: u64 = 0;
    let mut v_fold_2740_: u64 = 0;
    let mut v___x_2741_: u64 = 0;
    let mut v___x_2742_: u64 = 0;
    let mut v___x_2743_: u64 = 0;
    let mut v___x_2744_: usize = 0;
    let mut v___x_2745_: usize = 0;
    let mut v___x_2746_: usize = 0;
    let mut v___x_2747_: usize = 0;
    let mut v___x_2748_: usize = 0;
    let mut v_bkt_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v_val_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut v_unused_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2732_ = leanh::lean_ctor_get(v_m_2729_, 0);
                v_buckets_2733_ = leanh::lean_ctor_get(v_m_2729_, 1);
                v___x_2734_ = lean_array_get_size(v_buckets_2733_);
                leanh::lean_inc_ref(v_x_2728_);
                leanh::lean_inc_n(v_a_2730_, 2);
                v___x_2735_ = leanh::lean_apply_1(v_x_2728_, v_a_2730_);
                v___x_2736_ = 32u64;
                v___x_2737_ = leanh::lean_unbox_uint64(v___x_2735_);
                v___x_2738_ = lean_uint64_shift_right(v___x_2737_, v___x_2736_);
                v___x_2739_ = leanh::lean_unbox_uint64(v___x_2735_);
                leanh::lean_dec_ref(v___x_2735_);
                v_fold_2740_ = lean_uint64_xor(v___x_2739_, v___x_2738_);
                v___x_2741_ = 16u64;
                v___x_2742_ = lean_uint64_shift_right(v_fold_2740_, v___x_2741_);
                v___x_2743_ = lean_uint64_xor(v_fold_2740_, v___x_2742_);
                v___x_2744_ = lean_uint64_to_usize(v___x_2743_);
                v___x_2745_ = lean_usize_of_nat(v___x_2734_);
                v___x_2746_ = 1usize;
                v___x_2747_ = lean_usize_sub(v___x_2745_, v___x_2746_);
                v___x_2748_ = lean_usize_land(v___x_2744_, v___x_2747_);
                v_bkt_2749_ = lean_array_uget_borrowed(v_buckets_2733_, v___x_2748_);
                leanh::lean_inc(v_bkt_2749_);
                v___x_2750_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2727_,
                    v_a_2730_,
                    v_bkt_2749_,
                );
                if leanh::lean_obj_tag(v___x_2750_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2733_);
                    leanh::lean_inc(v_size_2732_);
                    v_isSharedCheck_2773_ = (!leanh::lean_is_exclusive(v_m_2729_)) as u8;
                    if v_isSharedCheck_2773_ == 0 {
                        v_unused_2774_ = leanh::lean_ctor_get(v_m_2729_, 1);
                        leanh::lean_dec(v_unused_2774_);
                        v_unused_2775_ = leanh::lean_ctor_get(v_m_2729_, 0);
                        leanh::lean_dec(v_unused_2775_);
                        v___x_2752_ = v_m_2729_;
                        v_isShared_2753_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2729_);
                        v___x_2752_ = leanh::lean_box(0);
                        v_isShared_2753_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2731_);
                    leanh::lean_dec(v_a_2730_);
                    leanh::lean_dec_ref(v_x_2728_);
                    v___x_2776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2776_, 0, v___x_2750_);
                    leanh::lean_ctor_set(v___x_2776_, 1, v_m_2729_);
                    return v___x_2776_;
                }
            }
            1 => {
                v___x_2754_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2755_ = lean_nat_add(v_size_2732_, v___x_2754_);
                leanh::lean_dec(v_size_2732_);
                leanh::lean_inc(v_bkt_2749_);
                v___x_2756_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2756_, 0, v_a_2730_);
                leanh::lean_ctor_set(v___x_2756_, 1, v_b_2731_);
                leanh::lean_ctor_set(v___x_2756_, 2, v_bkt_2749_);
                v_buckets_x27_2757_ = lean_array_uset(v_buckets_2733_, v___x_2748_, v___x_2756_);
                v___x_2758_ = leanh::lean_unsigned_to_nat(4);
                v___x_2759_ = lean_nat_mul(v_size_x27_2755_, v___x_2758_);
                v___x_2760_ = leanh::lean_unsigned_to_nat(3);
                v___x_2761_ = lean_nat_div(v___x_2759_, v___x_2760_);
                leanh::lean_dec(v___x_2759_);
                v___x_2762_ = lean_array_get_size(v_buckets_x27_2757_);
                v___x_2763_ = lean_nat_dec_le(v___x_2761_, v___x_2762_);
                leanh::lean_dec(v___x_2761_);
                if v___x_2763_ == 0 {
                    v_val_2764_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2728_,
                        v_buckets_x27_2757_,
                    );
                    if v_isShared_2753_ == 0 {
                        leanh::lean_ctor_set(v___x_2752_, 1, v_val_2764_);
                        leanh::lean_ctor_set(v___x_2752_, 0, v_size_x27_2755_);
                        v___x_2766_ = v___x_2752_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_size_x27_2755_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_val_2764_);
                        v___x_2766_ = v_reuseFailAlloc_2768_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2728_);
                    if v_isShared_2753_ == 0 {
                        leanh::lean_ctor_set(v___x_2752_, 1, v_buckets_x27_2757_);
                        leanh::lean_ctor_set(v___x_2752_, 0, v_size_x27_2755_);
                        v___x_2770_ = v___x_2752_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2772_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_size_x27_2755_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_buckets_x27_2757_);
                        v___x_2770_ = v_reuseFailAlloc_2772_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2767_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2767_, 0, v___x_2750_);
                leanh::lean_ctor_set(v___x_2767_, 1, v___x_2766_);
                return v___x_2767_;
            }
            3 => {
                v___x_2771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2771_, 0, v___x_2750_);
                leanh::lean_ctor_set(v___x_2771_, 1, v___x_2770_);
                return v___x_2771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_getThenInsertIfNew_x3f(
    mut v_00_u03b1_2777_: *mut leanh::LeanObject,
    mut v_00_u03b2_2778_: *mut leanh::LeanObject,
    mut v_x_2779_: *mut leanh::LeanObject,
    mut v_x_2780_: *mut leanh::LeanObject,
    mut v_m_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_b_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u64 = 0;
    let mut v___x_2789_: u64 = 0;
    let mut v___x_2790_: u64 = 0;
    let mut v___x_2791_: u64 = 0;
    let mut v_fold_2792_: u64 = 0;
    let mut v___x_2793_: u64 = 0;
    let mut v___x_2794_: u64 = 0;
    let mut v___x_2795_: u64 = 0;
    let mut v___x_2796_: usize = 0;
    let mut v___x_2797_: usize = 0;
    let mut v___x_2798_: usize = 0;
    let mut v___x_2799_: usize = 0;
    let mut v___x_2800_: usize = 0;
    let mut v_bkt_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2805_: u8 = 0;
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v_val_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2825_: u8 = 0;
    let mut v_unused_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2784_ = leanh::lean_ctor_get(v_m_2781_, 0);
                v_buckets_2785_ = leanh::lean_ctor_get(v_m_2781_, 1);
                v___x_2786_ = lean_array_get_size(v_buckets_2785_);
                leanh::lean_inc_ref(v_x_2780_);
                leanh::lean_inc_n(v_a_2782_, 2);
                v___x_2787_ = leanh::lean_apply_1(v_x_2780_, v_a_2782_);
                v___x_2788_ = 32u64;
                v___x_2789_ = leanh::lean_unbox_uint64(v___x_2787_);
                v___x_2790_ = lean_uint64_shift_right(v___x_2789_, v___x_2788_);
                v___x_2791_ = leanh::lean_unbox_uint64(v___x_2787_);
                leanh::lean_dec_ref(v___x_2787_);
                v_fold_2792_ = lean_uint64_xor(v___x_2791_, v___x_2790_);
                v___x_2793_ = 16u64;
                v___x_2794_ = lean_uint64_shift_right(v_fold_2792_, v___x_2793_);
                v___x_2795_ = lean_uint64_xor(v_fold_2792_, v___x_2794_);
                v___x_2796_ = lean_uint64_to_usize(v___x_2795_);
                v___x_2797_ = lean_usize_of_nat(v___x_2786_);
                v___x_2798_ = 1usize;
                v___x_2799_ = lean_usize_sub(v___x_2797_, v___x_2798_);
                v___x_2800_ = lean_usize_land(v___x_2796_, v___x_2799_);
                v_bkt_2801_ = lean_array_uget_borrowed(v_buckets_2785_, v___x_2800_);
                leanh::lean_inc(v_bkt_2801_);
                v___x_2802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_x_2779_,
                    v_a_2782_,
                    v_bkt_2801_,
                );
                if leanh::lean_obj_tag(v___x_2802_) == 0 {
                    leanh::lean_inc_ref(v_buckets_2785_);
                    leanh::lean_inc(v_size_2784_);
                    v_isSharedCheck_2825_ = (!leanh::lean_is_exclusive(v_m_2781_)) as u8;
                    if v_isSharedCheck_2825_ == 0 {
                        v_unused_2826_ = leanh::lean_ctor_get(v_m_2781_, 1);
                        leanh::lean_dec(v_unused_2826_);
                        v_unused_2827_ = leanh::lean_ctor_get(v_m_2781_, 0);
                        leanh::lean_dec(v_unused_2827_);
                        v___x_2804_ = v_m_2781_;
                        v_isShared_2805_ = v_isSharedCheck_2825_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2781_);
                        v___x_2804_ = leanh::lean_box(0);
                        v_isShared_2805_ = v_isSharedCheck_2825_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2783_);
                    leanh::lean_dec(v_a_2782_);
                    leanh::lean_dec_ref(v_x_2780_);
                    v___x_2828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2828_, 0, v___x_2802_);
                    leanh::lean_ctor_set(v___x_2828_, 1, v_m_2781_);
                    return v___x_2828_;
                }
            }
            1 => {
                v___x_2806_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2807_ = lean_nat_add(v_size_2784_, v___x_2806_);
                leanh::lean_dec(v_size_2784_);
                leanh::lean_inc(v_bkt_2801_);
                v___x_2808_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2808_, 0, v_a_2782_);
                leanh::lean_ctor_set(v___x_2808_, 1, v_b_2783_);
                leanh::lean_ctor_set(v___x_2808_, 2, v_bkt_2801_);
                v_buckets_x27_2809_ = lean_array_uset(v_buckets_2785_, v___x_2800_, v___x_2808_);
                v___x_2810_ = leanh::lean_unsigned_to_nat(4);
                v___x_2811_ = lean_nat_mul(v_size_x27_2807_, v___x_2810_);
                v___x_2812_ = leanh::lean_unsigned_to_nat(3);
                v___x_2813_ = lean_nat_div(v___x_2811_, v___x_2812_);
                leanh::lean_dec(v___x_2811_);
                v___x_2814_ = lean_array_get_size(v_buckets_x27_2809_);
                v___x_2815_ = lean_nat_dec_le(v___x_2813_, v___x_2814_);
                leanh::lean_dec(v___x_2813_);
                if v___x_2815_ == 0 {
                    v_val_2816_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_2780_,
                        v_buckets_x27_2809_,
                    );
                    if v_isShared_2805_ == 0 {
                        leanh::lean_ctor_set(v___x_2804_, 1, v_val_2816_);
                        leanh::lean_ctor_set(v___x_2804_, 0, v_size_x27_2807_);
                        v___x_2818_ = v___x_2804_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2820_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_size_x27_2807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_val_2816_);
                        v___x_2818_ = v_reuseFailAlloc_2820_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2780_);
                    if v_isShared_2805_ == 0 {
                        leanh::lean_ctor_set(v___x_2804_, 1, v_buckets_x27_2809_);
                        leanh::lean_ctor_set(v___x_2804_, 0, v_size_x27_2807_);
                        v___x_2822_ = v___x_2804_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_size_x27_2807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_buckets_x27_2809_);
                        v___x_2822_ = v_reuseFailAlloc_2824_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2819_, 0, v___x_2802_);
                leanh::lean_ctor_set(v___x_2819_, 1, v___x_2818_);
                return v___x_2819_;
            }
            3 => {
                v___x_2823_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2823_, 0, v___x_2802_);
                leanh::lean_ctor_set(v___x_2823_, 1, v___x_2822_);
                return v___x_2823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_get_x3f___redArg(
    mut v_x_2829_: *mut leanh::LeanObject,
    mut v_x_2830_: *mut leanh::LeanObject,
    mut v_m_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2829_, v_x_2830_, v_m_2831_, v_a_2832_,
    );
    return v___x_2833_;
}
pub unsafe fn l_Std_HashMap_get_x3f___redArg___boxed(
    mut v_x_2834_: *mut leanh::LeanObject,
    mut v_x_2835_: *mut leanh::LeanObject,
    mut v_m_2836_: *mut leanh::LeanObject,
    mut v_a_2837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2838_ = l_Std_HashMap_get_x3f___redArg(v_x_2834_, v_x_2835_, v_m_2836_, v_a_2837_);
    leanh::lean_dec_ref(v_m_2836_);
    return v_res_2838_;
}
pub unsafe fn l_Std_HashMap_get_x3f(
    mut v_00_u03b1_2839_: *mut leanh::LeanObject,
    mut v_00_u03b2_2840_: *mut leanh::LeanObject,
    mut v_x_2841_: *mut leanh::LeanObject,
    mut v_x_2842_: *mut leanh::LeanObject,
    mut v_m_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_x_2841_, v_x_2842_, v_m_2843_, v_a_2844_,
    );
    return v___x_2845_;
}
pub unsafe fn l_Std_HashMap_get_x3f___boxed(
    mut v_00_u03b1_2846_: *mut leanh::LeanObject,
    mut v_00_u03b2_2847_: *mut leanh::LeanObject,
    mut v_x_2848_: *mut leanh::LeanObject,
    mut v_x_2849_: *mut leanh::LeanObject,
    mut v_m_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Std_HashMap_get_x3f(
        v_00_u03b1_2846_,
        v_00_u03b2_2847_,
        v_x_2848_,
        v_x_2849_,
        v_m_2850_,
        v_a_2851_,
    );
    leanh::lean_dec_ref(v_m_2850_);
    return v_res_2852_;
}
pub unsafe fn l_Std_HashMap_contains___redArg(
    mut v_x_2853_: *mut leanh::LeanObject,
    mut v_x_2854_: *mut leanh::LeanObject,
    mut v_m_2855_: *mut leanh::LeanObject,
    mut v_a_2856_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2857_: u8 = 0;
    v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2853_, v_x_2854_, v_m_2855_, v_a_2856_,
    );
    return v___x_2857_;
}
pub unsafe fn l_Std_HashMap_contains___redArg___boxed(
    mut v_x_2858_: *mut leanh::LeanObject,
    mut v_x_2859_: *mut leanh::LeanObject,
    mut v_m_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2862_: u8 = 0;
    let mut v_r_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Std_HashMap_contains___redArg(v_x_2858_, v_x_2859_, v_m_2860_, v_a_2861_);
    leanh::lean_dec_ref(v_m_2860_);
    v_r_2863_ = leanh::lean_box((v_res_2862_) as usize);
    return v_r_2863_;
}
pub unsafe fn l_Std_HashMap_contains(
    mut v_00_u03b1_2864_: *mut leanh::LeanObject,
    mut v_00_u03b2_2865_: *mut leanh::LeanObject,
    mut v_x_2866_: *mut leanh::LeanObject,
    mut v_x_2867_: *mut leanh::LeanObject,
    mut v_m_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2870_: u8 = 0;
    v___x_2870_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_2866_, v_x_2867_, v_m_2868_, v_a_2869_,
    );
    return v___x_2870_;
}
pub unsafe fn l_Std_HashMap_contains___boxed(
    mut v_00_u03b1_2871_: *mut leanh::LeanObject,
    mut v_00_u03b2_2872_: *mut leanh::LeanObject,
    mut v_x_2873_: *mut leanh::LeanObject,
    mut v_x_2874_: *mut leanh::LeanObject,
    mut v_m_2875_: *mut leanh::LeanObject,
    mut v_a_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2877_: u8 = 0;
    let mut v_r_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Std_HashMap_contains(
        v_00_u03b1_2871_,
        v_00_u03b2_2872_,
        v_x_2873_,
        v_x_2874_,
        v_m_2875_,
        v_a_2876_,
    );
    leanh::lean_dec_ref(v_m_2875_);
    v_r_2878_ = leanh::lean_box((v_res_2877_) as usize);
    return v_r_2878_;
}
pub unsafe fn l_Std_HashMap_instMembership(
    mut v_00_u03b1_2879_: *mut leanh::LeanObject,
    mut v_00_u03b2_2880_: *mut leanh::LeanObject,
    mut v_inst_2881_: *mut leanh::LeanObject,
    mut v_inst_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = leanh::lean_box(0);
    return v___x_2883_;
}
pub unsafe fn l_Std_HashMap_instMembership___boxed(
    mut v_00_u03b1_2884_: *mut leanh::LeanObject,
    mut v_00_u03b2_2885_: *mut leanh::LeanObject,
    mut v_inst_2886_: *mut leanh::LeanObject,
    mut v_inst_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_Std_HashMap_instMembership(
        v_00_u03b1_2884_,
        v_00_u03b2_2885_,
        v_inst_2886_,
        v_inst_2887_,
    );
    leanh::lean_dec_ref(v_inst_2887_);
    leanh::lean_dec_ref(v_inst_2886_);
    return v_res_2888_;
}
pub unsafe fn l_Std_HashMap_instDecidableMem___redArg(
    mut v_inst_2889_: *mut leanh::LeanObject,
    mut v_inst_2890_: *mut leanh::LeanObject,
    mut v_m_2891_: *mut leanh::LeanObject,
    mut v_a_2892_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2893_: u8 = 0;
    v___x_2893_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2889_,
        v_inst_2890_,
        v_m_2891_,
        v_a_2892_,
    );
    return v___x_2893_;
}
pub unsafe fn l_Std_HashMap_instDecidableMem___redArg___boxed(
    mut v_inst_2894_: *mut leanh::LeanObject,
    mut v_inst_2895_: *mut leanh::LeanObject,
    mut v_m_2896_: *mut leanh::LeanObject,
    mut v_a_2897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2898_: u8 = 0;
    let mut v_r_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ =
        l_Std_HashMap_instDecidableMem___redArg(v_inst_2894_, v_inst_2895_, v_m_2896_, v_a_2897_);
    leanh::lean_dec_ref(v_m_2896_);
    v_r_2899_ = leanh::lean_box((v_res_2898_) as usize);
    return v_r_2899_;
}
pub unsafe fn l_Std_HashMap_instDecidableMem(
    mut v_00_u03b1_2900_: *mut leanh::LeanObject,
    mut v_00_u03b2_2901_: *mut leanh::LeanObject,
    mut v_inst_2902_: *mut leanh::LeanObject,
    mut v_inst_2903_: *mut leanh::LeanObject,
    mut v_m_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2906_: u8 = 0;
    v___x_2906_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2902_,
        v_inst_2903_,
        v_m_2904_,
        v_a_2905_,
    );
    return v___x_2906_;
}
pub unsafe fn l_Std_HashMap_instDecidableMem___boxed(
    mut v_00_u03b1_2907_: *mut leanh::LeanObject,
    mut v_00_u03b2_2908_: *mut leanh::LeanObject,
    mut v_inst_2909_: *mut leanh::LeanObject,
    mut v_inst_2910_: *mut leanh::LeanObject,
    mut v_m_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2913_: u8 = 0;
    let mut v_r_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Std_HashMap_instDecidableMem(
        v_00_u03b1_2907_,
        v_00_u03b2_2908_,
        v_inst_2909_,
        v_inst_2910_,
        v_m_2911_,
        v_a_2912_,
    );
    leanh::lean_dec_ref(v_m_2911_);
    v_r_2914_ = leanh::lean_box((v_res_2913_) as usize);
    return v_r_2914_;
}
pub unsafe fn l_Std_HashMap_get___redArg(
    mut v_x_2915_: *mut leanh::LeanObject,
    mut v_x_2916_: *mut leanh::LeanObject,
    mut v_m_2917_: *mut leanh::LeanObject,
    mut v_a_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2915_, v_x_2916_, v_m_2917_, v_a_2918_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Std_HashMap_get___redArg___boxed(
    mut v_x_2920_: *mut leanh::LeanObject,
    mut v_x_2921_: *mut leanh::LeanObject,
    mut v_m_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Std_HashMap_get___redArg(v_x_2920_, v_x_2921_, v_m_2922_, v_a_2923_);
    leanh::lean_dec_ref(v_m_2922_);
    return v_res_2924_;
}
pub unsafe fn l_Std_HashMap_get(
    mut v_00_u03b1_2925_: *mut leanh::LeanObject,
    mut v_00_u03b2_2926_: *mut leanh::LeanObject,
    mut v_x_2927_: *mut leanh::LeanObject,
    mut v_x_2928_: *mut leanh::LeanObject,
    mut v_m_2929_: *mut leanh::LeanObject,
    mut v_a_2930_: *mut leanh::LeanObject,
    mut v_h_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_x_2927_, v_x_2928_, v_m_2929_, v_a_2930_,
    );
    return v___x_2932_;
}
pub unsafe fn l_Std_HashMap_get___boxed(
    mut v_00_u03b1_2933_: *mut leanh::LeanObject,
    mut v_00_u03b2_2934_: *mut leanh::LeanObject,
    mut v_x_2935_: *mut leanh::LeanObject,
    mut v_x_2936_: *mut leanh::LeanObject,
    mut v_m_2937_: *mut leanh::LeanObject,
    mut v_a_2938_: *mut leanh::LeanObject,
    mut v_h_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_HashMap_get(
        v_00_u03b1_2933_,
        v_00_u03b2_2934_,
        v_x_2935_,
        v_x_2936_,
        v_m_2937_,
        v_a_2938_,
        v_h_2939_,
    );
    leanh::lean_dec_ref(v_m_2937_);
    return v_res_2940_;
}
pub unsafe fn l_Std_HashMap_getD___redArg(
    mut v_x_2941_: *mut leanh::LeanObject,
    mut v_x_2942_: *mut leanh::LeanObject,
    mut v_m_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
    mut v_fallback_2945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_2941_,
        v_x_2942_,
        v_m_2943_,
        v_a_2944_,
        v_fallback_2945_,
    );
    return v___x_2946_;
}
pub unsafe fn l_Std_HashMap_getD___redArg___boxed(
    mut v_x_2947_: *mut leanh::LeanObject,
    mut v_x_2948_: *mut leanh::LeanObject,
    mut v_m_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_fallback_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ =
        l_Std_HashMap_getD___redArg(v_x_2947_, v_x_2948_, v_m_2949_, v_a_2950_, v_fallback_2951_);
    leanh::lean_dec(v_fallback_2951_);
    leanh::lean_dec_ref(v_m_2949_);
    return v_res_2952_;
}
pub unsafe fn l_Std_HashMap_getD(
    mut v_00_u03b1_2953_: *mut leanh::LeanObject,
    mut v_00_u03b2_2954_: *mut leanh::LeanObject,
    mut v_x_2955_: *mut leanh::LeanObject,
    mut v_x_2956_: *mut leanh::LeanObject,
    mut v_m_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
    mut v_fallback_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_x_2955_,
        v_x_2956_,
        v_m_2957_,
        v_a_2958_,
        v_fallback_2959_,
    );
    return v___x_2960_;
}
pub unsafe fn l_Std_HashMap_getD___boxed(
    mut v_00_u03b1_2961_: *mut leanh::LeanObject,
    mut v_00_u03b2_2962_: *mut leanh::LeanObject,
    mut v_x_2963_: *mut leanh::LeanObject,
    mut v_x_2964_: *mut leanh::LeanObject,
    mut v_m_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_fallback_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Std_HashMap_getD(
        v_00_u03b1_2961_,
        v_00_u03b2_2962_,
        v_x_2963_,
        v_x_2964_,
        v_m_2965_,
        v_a_2966_,
        v_fallback_2967_,
    );
    leanh::lean_dec(v_fallback_2967_);
    leanh::lean_dec_ref(v_m_2965_);
    return v_res_2968_;
}
pub unsafe fn l_Std_HashMap_get_x21___redArg(
    mut v_x_2969_: *mut leanh::LeanObject,
    mut v_x_2970_: *mut leanh::LeanObject,
    mut v_inst_2971_: *mut leanh::LeanObject,
    mut v_m_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_2969_,
        v_x_2970_,
        v_inst_2971_,
        v_m_2972_,
        v_a_2973_,
    );
    return v___x_2974_;
}
pub unsafe fn l_Std_HashMap_get_x21___redArg___boxed(
    mut v_x_2975_: *mut leanh::LeanObject,
    mut v_x_2976_: *mut leanh::LeanObject,
    mut v_inst_2977_: *mut leanh::LeanObject,
    mut v_m_2978_: *mut leanh::LeanObject,
    mut v_a_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2980_ =
        l_Std_HashMap_get_x21___redArg(v_x_2975_, v_x_2976_, v_inst_2977_, v_m_2978_, v_a_2979_);
    leanh::lean_dec_ref(v_m_2978_);
    leanh::lean_dec(v_inst_2977_);
    return v_res_2980_;
}
pub unsafe fn l_Std_HashMap_get_x21(
    mut v_00_u03b1_2981_: *mut leanh::LeanObject,
    mut v_00_u03b2_2982_: *mut leanh::LeanObject,
    mut v_x_2983_: *mut leanh::LeanObject,
    mut v_x_2984_: *mut leanh::LeanObject,
    mut v_inst_2985_: *mut leanh::LeanObject,
    mut v_m_2986_: *mut leanh::LeanObject,
    mut v_a_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_x_2983_,
        v_x_2984_,
        v_inst_2985_,
        v_m_2986_,
        v_a_2987_,
    );
    return v___x_2988_;
}
pub unsafe fn l_Std_HashMap_get_x21___boxed(
    mut v_00_u03b1_2989_: *mut leanh::LeanObject,
    mut v_00_u03b2_2990_: *mut leanh::LeanObject,
    mut v_x_2991_: *mut leanh::LeanObject,
    mut v_x_2992_: *mut leanh::LeanObject,
    mut v_inst_2993_: *mut leanh::LeanObject,
    mut v_m_2994_: *mut leanh::LeanObject,
    mut v_a_2995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2996_ = l_Std_HashMap_get_x21(
        v_00_u03b1_2989_,
        v_00_u03b2_2990_,
        v_x_2991_,
        v_x_2992_,
        v_inst_2993_,
        v_m_2994_,
        v_a_2995_,
    );
    leanh::lean_dec_ref(v_m_2994_);
    leanh::lean_dec(v_inst_2993_);
    return v_res_2996_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(
    mut v_inst_2997_: *mut leanh::LeanObject,
    mut v_inst_2998_: *mut leanh::LeanObject,
    mut v_m_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_h_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_2997_,
        v_inst_2998_,
        v_m_2999_,
        v_a_3000_,
    );
    return v___x_3002_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(
    mut v_inst_3003_: *mut leanh::LeanObject,
    mut v_inst_3004_: *mut leanh::LeanObject,
    mut v_m_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_h_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(
        v_inst_3003_,
        v_inst_3004_,
        v_m_3005_,
        v_a_3006_,
        v_h_3007_,
    );
    leanh::lean_dec_ref(v_m_3005_);
    return v_res_3008_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(
    mut v_inst_3009_: *mut leanh::LeanObject,
    mut v_inst_3010_: *mut leanh::LeanObject,
    mut v_m_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_3009_,
        v_inst_3010_,
        v_m_3011_,
        v_a_3012_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(
    mut v_inst_3014_: *mut leanh::LeanObject,
    mut v_inst_3015_: *mut leanh::LeanObject,
    mut v_m_3016_: *mut leanh::LeanObject,
    mut v_a_3017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(
        v_inst_3014_,
        v_inst_3015_,
        v_m_3016_,
        v_a_3017_,
    );
    leanh::lean_dec_ref(v_m_3016_);
    return v_res_3018_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(
    mut v_inst_3019_: *mut leanh::LeanObject,
    mut v_inst_3020_: *mut leanh::LeanObject,
    mut v_inst_3021_: *mut leanh::LeanObject,
    mut v_m_3022_: *mut leanh::LeanObject,
    mut v_a_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_inst_3019_,
        v_inst_3020_,
        v_inst_3021_,
        v_m_3022_,
        v_a_3023_,
    );
    return v___x_3024_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(
    mut v_inst_3025_: *mut leanh::LeanObject,
    mut v_inst_3026_: *mut leanh::LeanObject,
    mut v_inst_3027_: *mut leanh::LeanObject,
    mut v_m_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3030_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(
        v_inst_3025_,
        v_inst_3026_,
        v_inst_3027_,
        v_m_3028_,
        v_a_3029_,
    );
    leanh::lean_dec_ref(v_m_3028_);
    leanh::lean_dec(v_inst_3027_);
    return v_res_3030_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem___redArg(
    mut v_inst_3031_: *mut leanh::LeanObject,
    mut v_inst_3032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_3032_, 2);
    leanh::lean_inc_ref_n(v_inst_3031_, 2);
    v___f_3033_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3033_, 0, v_inst_3031_);
    leanh::lean_closure_set(v___f_3033_, 1, v_inst_3032_);
    v___f_3034_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3034_, 0, v_inst_3031_);
    leanh::lean_closure_set(v___f_3034_, 1, v_inst_3032_);
    v___f_3035_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3035_, 0, v_inst_3031_);
    leanh::lean_closure_set(v___f_3035_, 1, v_inst_3032_);
    v___x_3036_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3036_, 0, v___f_3033_);
    leanh::lean_ctor_set(v___x_3036_, 1, v___f_3034_);
    leanh::lean_ctor_set(v___x_3036_, 2, v___f_3035_);
    return v___x_3036_;
}
pub unsafe fn l_Std_HashMap_instGetElem_x3fMem(
    mut v_00_u03b1_3037_: *mut leanh::LeanObject,
    mut v_00_u03b2_3038_: *mut leanh::LeanObject,
    mut v_inst_3039_: *mut leanh::LeanObject,
    mut v_inst_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3041_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_3039_, v_inst_3040_);
    return v___x_3041_;
}
pub unsafe fn l_Std_HashMap_getKey_x3f___redArg(
    mut v_x_3042_: *mut leanh::LeanObject,
    mut v_x_3043_: *mut leanh::LeanObject,
    mut v_m_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3046_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_3042_, v_x_3043_, v_m_3044_, v_a_3045_,
    );
    return v___x_3046_;
}
pub unsafe fn l_Std_HashMap_getKey_x3f___redArg___boxed(
    mut v_x_3047_: *mut leanh::LeanObject,
    mut v_x_3048_: *mut leanh::LeanObject,
    mut v_m_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Std_HashMap_getKey_x3f___redArg(v_x_3047_, v_x_3048_, v_m_3049_, v_a_3050_);
    leanh::lean_dec_ref(v_m_3049_);
    return v_res_3051_;
}
pub unsafe fn l_Std_HashMap_getKey_x3f(
    mut v_00_u03b1_3052_: *mut leanh::LeanObject,
    mut v_00_u03b2_3053_: *mut leanh::LeanObject,
    mut v_x_3054_: *mut leanh::LeanObject,
    mut v_x_3055_: *mut leanh::LeanObject,
    mut v_m_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3058_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_3054_, v_x_3055_, v_m_3056_, v_a_3057_,
    );
    return v___x_3058_;
}
pub unsafe fn l_Std_HashMap_getKey_x3f___boxed(
    mut v_00_u03b1_3059_: *mut leanh::LeanObject,
    mut v_00_u03b2_3060_: *mut leanh::LeanObject,
    mut v_x_3061_: *mut leanh::LeanObject,
    mut v_x_3062_: *mut leanh::LeanObject,
    mut v_m_3063_: *mut leanh::LeanObject,
    mut v_a_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3065_ = l_Std_HashMap_getKey_x3f(
        v_00_u03b1_3059_,
        v_00_u03b2_3060_,
        v_x_3061_,
        v_x_3062_,
        v_m_3063_,
        v_a_3064_,
    );
    leanh::lean_dec_ref(v_m_3063_);
    return v_res_3065_;
}
pub unsafe fn l_Std_HashMap_getKey___redArg(
    mut v_x_3066_: *mut leanh::LeanObject,
    mut v_x_3067_: *mut leanh::LeanObject,
    mut v_m_3068_: *mut leanh::LeanObject,
    mut v_a_3069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_3066_, v_x_3067_, v_m_3068_, v_a_3069_,
    );
    return v___x_3070_;
}
pub unsafe fn l_Std_HashMap_getKey___redArg___boxed(
    mut v_x_3071_: *mut leanh::LeanObject,
    mut v_x_3072_: *mut leanh::LeanObject,
    mut v_m_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Std_HashMap_getKey___redArg(v_x_3071_, v_x_3072_, v_m_3073_, v_a_3074_);
    leanh::lean_dec_ref(v_m_3073_);
    return v_res_3075_;
}
pub unsafe fn l_Std_HashMap_getKey(
    mut v_00_u03b1_3076_: *mut leanh::LeanObject,
    mut v_00_u03b2_3077_: *mut leanh::LeanObject,
    mut v_x_3078_: *mut leanh::LeanObject,
    mut v_x_3079_: *mut leanh::LeanObject,
    mut v_m_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
    mut v_h_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_3078_, v_x_3079_, v_m_3080_, v_a_3081_,
    );
    return v___x_3083_;
}
pub unsafe fn l_Std_HashMap_getKey___boxed(
    mut v_00_u03b1_3084_: *mut leanh::LeanObject,
    mut v_00_u03b2_3085_: *mut leanh::LeanObject,
    mut v_x_3086_: *mut leanh::LeanObject,
    mut v_x_3087_: *mut leanh::LeanObject,
    mut v_m_3088_: *mut leanh::LeanObject,
    mut v_a_3089_: *mut leanh::LeanObject,
    mut v_h_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3091_ = l_Std_HashMap_getKey(
        v_00_u03b1_3084_,
        v_00_u03b2_3085_,
        v_x_3086_,
        v_x_3087_,
        v_m_3088_,
        v_a_3089_,
        v_h_3090_,
    );
    leanh::lean_dec_ref(v_m_3088_);
    return v_res_3091_;
}
pub unsafe fn l_Std_HashMap_getKeyD___redArg(
    mut v_x_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
    mut v_m_3094_: *mut leanh::LeanObject,
    mut v_a_3095_: *mut leanh::LeanObject,
    mut v_fallback_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3097_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_3092_,
        v_x_3093_,
        v_m_3094_,
        v_a_3095_,
        v_fallback_3096_,
    );
    return v___x_3097_;
}
pub unsafe fn l_Std_HashMap_getKeyD___redArg___boxed(
    mut v_x_3098_: *mut leanh::LeanObject,
    mut v_x_3099_: *mut leanh::LeanObject,
    mut v_m_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_fallback_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ = l_Std_HashMap_getKeyD___redArg(
        v_x_3098_,
        v_x_3099_,
        v_m_3100_,
        v_a_3101_,
        v_fallback_3102_,
    );
    leanh::lean_dec(v_fallback_3102_);
    leanh::lean_dec_ref(v_m_3100_);
    return v_res_3103_;
}
pub unsafe fn l_Std_HashMap_getKeyD(
    mut v_00_u03b1_3104_: *mut leanh::LeanObject,
    mut v_00_u03b2_3105_: *mut leanh::LeanObject,
    mut v_x_3106_: *mut leanh::LeanObject,
    mut v_x_3107_: *mut leanh::LeanObject,
    mut v_m_3108_: *mut leanh::LeanObject,
    mut v_a_3109_: *mut leanh::LeanObject,
    mut v_fallback_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3111_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_3106_,
        v_x_3107_,
        v_m_3108_,
        v_a_3109_,
        v_fallback_3110_,
    );
    return v___x_3111_;
}
pub unsafe fn l_Std_HashMap_getKeyD___boxed(
    mut v_00_u03b1_3112_: *mut leanh::LeanObject,
    mut v_00_u03b2_3113_: *mut leanh::LeanObject,
    mut v_x_3114_: *mut leanh::LeanObject,
    mut v_x_3115_: *mut leanh::LeanObject,
    mut v_m_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
    mut v_fallback_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Std_HashMap_getKeyD(
        v_00_u03b1_3112_,
        v_00_u03b2_3113_,
        v_x_3114_,
        v_x_3115_,
        v_m_3116_,
        v_a_3117_,
        v_fallback_3118_,
    );
    leanh::lean_dec(v_fallback_3118_);
    leanh::lean_dec_ref(v_m_3116_);
    return v_res_3119_;
}
pub unsafe fn l_Std_HashMap_getKey_x21___redArg(
    mut v_x_3120_: *mut leanh::LeanObject,
    mut v_x_3121_: *mut leanh::LeanObject,
    mut v_inst_3122_: *mut leanh::LeanObject,
    mut v_m_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3125_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_3120_,
        v_x_3121_,
        v_inst_3122_,
        v_m_3123_,
        v_a_3124_,
    );
    return v___x_3125_;
}
pub unsafe fn l_Std_HashMap_getKey_x21___redArg___boxed(
    mut v_x_3126_: *mut leanh::LeanObject,
    mut v_x_3127_: *mut leanh::LeanObject,
    mut v_inst_3128_: *mut leanh::LeanObject,
    mut v_m_3129_: *mut leanh::LeanObject,
    mut v_a_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3131_ =
        l_Std_HashMap_getKey_x21___redArg(v_x_3126_, v_x_3127_, v_inst_3128_, v_m_3129_, v_a_3130_);
    leanh::lean_dec_ref(v_m_3129_);
    leanh::lean_dec(v_inst_3128_);
    return v_res_3131_;
}
pub unsafe fn l_Std_HashMap_getKey_x21(
    mut v_00_u03b1_3132_: *mut leanh::LeanObject,
    mut v_00_u03b2_3133_: *mut leanh::LeanObject,
    mut v_x_3134_: *mut leanh::LeanObject,
    mut v_x_3135_: *mut leanh::LeanObject,
    mut v_inst_3136_: *mut leanh::LeanObject,
    mut v_m_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_3134_,
        v_x_3135_,
        v_inst_3136_,
        v_m_3137_,
        v_a_3138_,
    );
    return v___x_3139_;
}
pub unsafe fn l_Std_HashMap_getKey_x21___boxed(
    mut v_00_u03b1_3140_: *mut leanh::LeanObject,
    mut v_00_u03b2_3141_: *mut leanh::LeanObject,
    mut v_x_3142_: *mut leanh::LeanObject,
    mut v_x_3143_: *mut leanh::LeanObject,
    mut v_inst_3144_: *mut leanh::LeanObject,
    mut v_m_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Std_HashMap_getKey_x21(
        v_00_u03b1_3140_,
        v_00_u03b2_3141_,
        v_x_3142_,
        v_x_3143_,
        v_inst_3144_,
        v_m_3145_,
        v_a_3146_,
    );
    leanh::lean_dec_ref(v_m_3145_);
    leanh::lean_dec(v_inst_3144_);
    return v_res_3147_;
}
pub unsafe fn l_Std_HashMap_erase___redArg(
    mut v_x_3148_: *mut leanh::LeanObject,
    mut v_x_3149_: *mut leanh::LeanObject,
    mut v_m_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3152_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_3148_, v_x_3149_, v_m_3150_, v_a_3151_,
    );
    return v___x_3152_;
}
pub unsafe fn l_Std_HashMap_erase(
    mut v_00_u03b1_3153_: *mut leanh::LeanObject,
    mut v_00_u03b2_3154_: *mut leanh::LeanObject,
    mut v_x_3155_: *mut leanh::LeanObject,
    mut v_x_3156_: *mut leanh::LeanObject,
    mut v_m_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_3155_, v_x_3156_, v_m_3157_, v_a_3158_,
    );
    return v___x_3159_;
}
pub unsafe fn l_Std_HashMap_size___redArg(
    mut v_m_3160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_3161_ = leanh::lean_ctor_get(v_m_3160_, 0);
    leanh::lean_inc(v_size_3161_);
    return v_size_3161_;
}
pub unsafe fn l_Std_HashMap_size___redArg___boxed(
    mut v_m_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3163_ = l_Std_HashMap_size___redArg(v_m_3162_);
    leanh::lean_dec_ref(v_m_3162_);
    return v_res_3163_;
}
pub unsafe fn l_Std_HashMap_size(
    mut v_00_u03b1_3164_: *mut leanh::LeanObject,
    mut v_00_u03b2_3165_: *mut leanh::LeanObject,
    mut v_x_3166_: *mut leanh::LeanObject,
    mut v_x_3167_: *mut leanh::LeanObject,
    mut v_m_3168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_3169_ = leanh::lean_ctor_get(v_m_3168_, 0);
    leanh::lean_inc(v_size_3169_);
    return v_size_3169_;
}
pub unsafe fn l_Std_HashMap_size___boxed(
    mut v_00_u03b1_3170_: *mut leanh::LeanObject,
    mut v_00_u03b2_3171_: *mut leanh::LeanObject,
    mut v_x_3172_: *mut leanh::LeanObject,
    mut v_x_3173_: *mut leanh::LeanObject,
    mut v_m_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Std_HashMap_size(
        v_00_u03b1_3170_,
        v_00_u03b2_3171_,
        v_x_3172_,
        v_x_3173_,
        v_m_3174_,
    );
    leanh::lean_dec_ref(v_m_3174_);
    leanh::lean_dec_ref(v_x_3173_);
    leanh::lean_dec_ref(v_x_3172_);
    return v_res_3175_;
}
pub unsafe fn l_Std_HashMap_isEmpty___redArg(mut v_m_3176_: *mut leanh::LeanObject) -> u8 {
    let mut v_size_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    v_size_3177_ = leanh::lean_ctor_get(v_m_3176_, 0);
    v___x_3178_ = leanh::lean_unsigned_to_nat(0);
    v___x_3179_ = lean_nat_dec_eq(v_size_3177_, v___x_3178_);
    return v___x_3179_;
}
pub unsafe fn l_Std_HashMap_isEmpty___redArg___boxed(
    mut v_m_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3181_: u8 = 0;
    let mut v_r_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3181_ = l_Std_HashMap_isEmpty___redArg(v_m_3180_);
    leanh::lean_dec_ref(v_m_3180_);
    v_r_3182_ = leanh::lean_box((v_res_3181_) as usize);
    return v_r_3182_;
}
pub unsafe fn l_Std_HashMap_isEmpty(
    mut v_00_u03b1_3183_: *mut leanh::LeanObject,
    mut v_00_u03b2_3184_: *mut leanh::LeanObject,
    mut v_x_3185_: *mut leanh::LeanObject,
    mut v_x_3186_: *mut leanh::LeanObject,
    mut v_m_3187_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    v_size_3188_ = leanh::lean_ctor_get(v_m_3187_, 0);
    v___x_3189_ = leanh::lean_unsigned_to_nat(0);
    v___x_3190_ = lean_nat_dec_eq(v_size_3188_, v___x_3189_);
    return v___x_3190_;
}
pub unsafe fn l_Std_HashMap_isEmpty___boxed(
    mut v_00_u03b1_3191_: *mut leanh::LeanObject,
    mut v_00_u03b2_3192_: *mut leanh::LeanObject,
    mut v_x_3193_: *mut leanh::LeanObject,
    mut v_x_3194_: *mut leanh::LeanObject,
    mut v_m_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3196_: u8 = 0;
    let mut v_r_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Std_HashMap_isEmpty(
        v_00_u03b1_3191_,
        v_00_u03b2_3192_,
        v_x_3193_,
        v_x_3194_,
        v_m_3195_,
    );
    leanh::lean_dec_ref(v_m_3195_);
    leanh::lean_dec_ref(v_x_3194_);
    leanh::lean_dec_ref(v_x_3193_);
    v_r_3197_ = leanh::lean_box((v_res_3196_) as usize);
    return v_r_3197_;
}
pub unsafe fn l_Std_HashMap_keys___redArg___lam__0(
    mut v_a_3198_: *mut leanh::LeanObject,
    mut v_b_3199_: *mut leanh::LeanObject,
    mut v_d_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3201_, 0, v_a_3198_);
    leanh::lean_ctor_set(v___x_3201_, 1, v_d_3200_);
    return v___x_3201_;
}
pub unsafe fn l_Std_HashMap_keys___redArg___lam__0___boxed(
    mut v_a_3202_: *mut leanh::LeanObject,
    mut v_b_3203_: *mut leanh::LeanObject,
    mut v_d_3204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3205_ = l_Std_HashMap_keys___redArg___lam__0(v_a_3202_, v_b_3203_, v_d_3204_);
    leanh::lean_dec(v_b_3203_);
    return v_res_3205_;
}
pub unsafe fn l_Std_HashMap_keys___redArg___lam__1(
    mut v___x_3206_: *mut leanh::LeanObject,
    mut v___f_3207_: *mut leanh::LeanObject,
    mut v_l_3208_: *mut leanh::LeanObject,
    mut v_acc_3209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3206_,
        v___f_3207_,
        v_acc_3209_,
        v_l_3208_,
    );
    return v___x_3210_;
}
pub unsafe fn l_Std_HashMap_keys___redArg(
    mut v_m_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    v___x_3235_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3236_ = leanh::lean_ctor_get(v_m_3234_, 1);
    leanh::lean_inc_ref(v_buckets_3236_);
    leanh::lean_dec_ref(v_m_3234_);
    v___x_3237_ = leanh::lean_box(0);
    v___x_3238_ = lean_array_get_size(v_buckets_3236_);
    v___x_3239_ = leanh::lean_unsigned_to_nat(0);
    v___x_3240_ = lean_nat_dec_lt(v___x_3239_, v___x_3238_);
    if v___x_3240_ == 0 {
        leanh::lean_dec_ref(v_buckets_3236_);
        return v___x_3237_;
    } else {
        let mut v___f_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: usize = 0;
        let mut v___x_3243_: usize = 0;
        let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3241_ = l_Std_HashMap_keys___redArg___closed__11;
        v___x_3242_ = lean_usize_of_nat(v___x_3238_);
        v___x_3243_ = 0usize;
        v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3235_,
            v___f_3241_,
            v_buckets_3236_,
            v___x_3242_,
            v___x_3243_,
            v___x_3237_,
        );
        return v___x_3244_;
    }
}
pub unsafe fn l_Std_HashMap_keys(
    mut v_00_u03b1_3245_: *mut leanh::LeanObject,
    mut v_00_u03b2_3246_: *mut leanh::LeanObject,
    mut v_x_3247_: *mut leanh::LeanObject,
    mut v_x_3248_: *mut leanh::LeanObject,
    mut v_m_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    v___x_3250_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3251_ = leanh::lean_ctor_get(v_m_3249_, 1);
    leanh::lean_inc_ref(v_buckets_3251_);
    leanh::lean_dec_ref(v_m_3249_);
    v___x_3252_ = leanh::lean_box(0);
    v___x_3253_ = lean_array_get_size(v_buckets_3251_);
    v___x_3254_ = leanh::lean_unsigned_to_nat(0);
    v___x_3255_ = lean_nat_dec_lt(v___x_3254_, v___x_3253_);
    if v___x_3255_ == 0 {
        leanh::lean_dec_ref(v_buckets_3251_);
        return v___x_3252_;
    } else {
        let mut v___f_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3257_: usize = 0;
        let mut v___x_3258_: usize = 0;
        let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3256_ = l_Std_HashMap_keys___redArg___closed__11;
        v___x_3257_ = lean_usize_of_nat(v___x_3253_);
        v___x_3258_ = 0usize;
        v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3250_,
            v___f_3256_,
            v_buckets_3251_,
            v___x_3257_,
            v___x_3258_,
            v___x_3252_,
        );
        return v___x_3259_;
    }
}
pub unsafe fn l_Std_HashMap_keys___boxed(
    mut v_00_u03b1_3260_: *mut leanh::LeanObject,
    mut v_00_u03b2_3261_: *mut leanh::LeanObject,
    mut v_x_3262_: *mut leanh::LeanObject,
    mut v_x_3263_: *mut leanh::LeanObject,
    mut v_m_3264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3265_ = l_Std_HashMap_keys(
        v_00_u03b1_3260_,
        v_00_u03b2_3261_,
        v_x_3262_,
        v_x_3263_,
        v_m_3264_,
    );
    leanh::lean_dec_ref(v_x_3263_);
    leanh::lean_dec_ref(v_x_3262_);
    return v_res_3265_;
}
pub unsafe fn l_Std_HashMap_ofList___redArg(
    mut v_inst_3270_: *mut leanh::LeanObject,
    mut v_inst_3271_: *mut leanh::LeanObject,
    mut v_l_3272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3273_ = l_Std_HashMap_ofList___redArg___closed__1;
    v___x_3274_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3273_,
        v_inst_3270_,
        v_inst_3271_,
        v___x_3274_,
        v_l_3272_,
    );
    return v___x_3275_;
}
pub unsafe fn l_Std_HashMap_ofList(
    mut v_00_u03b1_3276_: *mut leanh::LeanObject,
    mut v_00_u03b2_3277_: *mut leanh::LeanObject,
    mut v_inst_3278_: *mut leanh::LeanObject,
    mut v_inst_3279_: *mut leanh::LeanObject,
    mut v_l_3280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3281_ = l_Std_HashMap_ofList___redArg___closed__1;
    v___x_3282_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3281_,
        v_inst_3278_,
        v_inst_3279_,
        v___x_3282_,
        v_l_3280_,
    );
    return v___x_3283_;
}
pub unsafe fn l_Std_HashMap_unitOfList___redArg(
    mut v_inst_3284_: *mut leanh::LeanObject,
    mut v_inst_3285_: *mut leanh::LeanObject,
    mut v_l_3286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3287_ = l_Std_HashMap_ofList___redArg___closed__1;
    v___x_3288_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3287_,
        v_inst_3284_,
        v_inst_3285_,
        v___x_3288_,
        v_l_3286_,
    );
    return v___x_3289_;
}
pub unsafe fn l_Std_HashMap_unitOfList(
    mut v_00_u03b1_3290_: *mut leanh::LeanObject,
    mut v_inst_3291_: *mut leanh::LeanObject,
    mut v_inst_3292_: *mut leanh::LeanObject,
    mut v_l_3293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3294_ = l_Std_HashMap_ofList___redArg___closed__1;
    v___x_3295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_3294_,
        v_inst_3291_,
        v_inst_3292_,
        v___x_3295_,
        v_l_3293_,
    );
    return v___x_3296_;
}
pub unsafe fn l_Std_HashMap_ofArray___redArg(
    mut v_inst_3301_: *mut leanh::LeanObject,
    mut v_inst_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3304_ = l_Std_HashMap_ofArray___redArg___closed__1;
    v___x_3305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3304_,
        v_inst_3301_,
        v_inst_3302_,
        v___x_3305_,
        v_a_3303_,
    );
    return v___x_3306_;
}
pub unsafe fn l_Std_HashMap_ofArray(
    mut v_00_u03b1_3307_: *mut leanh::LeanObject,
    mut v_00_u03b2_3308_: *mut leanh::LeanObject,
    mut v_inst_3309_: *mut leanh::LeanObject,
    mut v_inst_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3312_ = l_Std_HashMap_ofArray___redArg___closed__1;
    v___x_3313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v___f_3312_,
        v_inst_3309_,
        v_inst_3310_,
        v___x_3313_,
        v_a_3311_,
    );
    return v___x_3314_;
}
pub unsafe fn l_Std_HashMap_toList___redArg___lam__0(
    mut v_a_3315_: *mut leanh::LeanObject,
    mut v_b_3316_: *mut leanh::LeanObject,
    mut v_d_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3318_, 0, v_a_3315_);
    leanh::lean_ctor_set(v___x_3318_, 1, v_b_3316_);
    v___x_3319_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3319_, 0, v___x_3318_);
    leanh::lean_ctor_set(v___x_3319_, 1, v_d_3317_);
    return v___x_3319_;
}
pub unsafe fn l_Std_HashMap_toList___redArg___lam__1(
    mut v___x_3320_: *mut leanh::LeanObject,
    mut v___f_3321_: *mut leanh::LeanObject,
    mut v_l_3322_: *mut leanh::LeanObject,
    mut v_acc_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_3320_,
        v___f_3321_,
        v_acc_3323_,
        v_l_3322_,
    );
    return v___x_3324_;
}
pub unsafe fn l_Std_HashMap_toList___redArg(
    mut v_m_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: u8 = 0;
    v___x_3330_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3331_ = leanh::lean_ctor_get(v_m_3329_, 1);
    leanh::lean_inc_ref(v_buckets_3331_);
    leanh::lean_dec_ref(v_m_3329_);
    v___x_3332_ = leanh::lean_box(0);
    v___x_3333_ = lean_array_get_size(v_buckets_3331_);
    v___x_3334_ = leanh::lean_unsigned_to_nat(0);
    v___x_3335_ = lean_nat_dec_lt(v___x_3334_, v___x_3333_);
    if v___x_3335_ == 0 {
        leanh::lean_dec_ref(v_buckets_3331_);
        return v___x_3332_;
    } else {
        let mut v___f_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3337_: usize = 0;
        let mut v___x_3338_: usize = 0;
        let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3336_ = l_Std_HashMap_toList___redArg___closed__1;
        v___x_3337_ = lean_usize_of_nat(v___x_3333_);
        v___x_3338_ = 0usize;
        v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3330_,
            v___f_3336_,
            v_buckets_3331_,
            v___x_3337_,
            v___x_3338_,
            v___x_3332_,
        );
        return v___x_3339_;
    }
}
pub unsafe fn l_Std_HashMap_toList(
    mut v_00_u03b1_3340_: *mut leanh::LeanObject,
    mut v_00_u03b2_3341_: *mut leanh::LeanObject,
    mut v_x_3342_: *mut leanh::LeanObject,
    mut v_x_3343_: *mut leanh::LeanObject,
    mut v_m_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    v___x_3345_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3346_ = leanh::lean_ctor_get(v_m_3344_, 1);
    leanh::lean_inc_ref(v_buckets_3346_);
    leanh::lean_dec_ref(v_m_3344_);
    v___x_3347_ = leanh::lean_box(0);
    v___x_3348_ = lean_array_get_size(v_buckets_3346_);
    v___x_3349_ = leanh::lean_unsigned_to_nat(0);
    v___x_3350_ = lean_nat_dec_lt(v___x_3349_, v___x_3348_);
    if v___x_3350_ == 0 {
        leanh::lean_dec_ref(v_buckets_3346_);
        return v___x_3347_;
    } else {
        let mut v___f_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3352_: usize = 0;
        let mut v___x_3353_: usize = 0;
        let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3351_ = l_Std_HashMap_toList___redArg___closed__1;
        v___x_3352_ = lean_usize_of_nat(v___x_3348_);
        v___x_3353_ = 0usize;
        v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3345_,
            v___f_3351_,
            v_buckets_3346_,
            v___x_3352_,
            v___x_3353_,
            v___x_3347_,
        );
        return v___x_3354_;
    }
}
pub unsafe fn l_Std_HashMap_toList___boxed(
    mut v_00_u03b1_3355_: *mut leanh::LeanObject,
    mut v_00_u03b2_3356_: *mut leanh::LeanObject,
    mut v_x_3357_: *mut leanh::LeanObject,
    mut v_x_3358_: *mut leanh::LeanObject,
    mut v_m_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Std_HashMap_toList(
        v_00_u03b1_3355_,
        v_00_u03b2_3356_,
        v_x_3357_,
        v_x_3358_,
        v_m_3359_,
    );
    leanh::lean_dec_ref(v_x_3358_);
    leanh::lean_dec_ref(v_x_3357_);
    return v_res_3360_;
}
pub unsafe fn l_Std_HashMap_foldM___redArg___lam__0(
    mut v_inst_3361_: *mut leanh::LeanObject,
    mut v_f_3362_: *mut leanh::LeanObject,
    mut v_acc_3363_: *mut leanh::LeanObject,
    mut v_l_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3361_,
        v_f_3362_,
        v_acc_3363_,
        v_l_3364_,
    );
    return v___x_3365_;
}
pub unsafe fn l_Std_HashMap_foldM___redArg(
    mut v_inst_3366_: *mut leanh::LeanObject,
    mut v_f_3367_: *mut leanh::LeanObject,
    mut v_init_3368_: *mut leanh::LeanObject,
    mut v_b_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u8 = 0;
    v_buckets_3370_ = leanh::lean_ctor_get(v_b_3369_, 1);
    leanh::lean_inc_ref(v_buckets_3370_);
    leanh::lean_dec_ref(v_b_3369_);
    v___x_3371_ = leanh::lean_unsigned_to_nat(0);
    v___x_3372_ = lean_array_get_size(v_buckets_3370_);
    v___x_3373_ = lean_nat_dec_lt(v___x_3371_, v___x_3372_);
    if v___x_3373_ == 0 {
        let mut v_toApplicative_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3370_);
        leanh::lean_dec(v_f_3367_);
        v_toApplicative_3374_ = leanh::lean_ctor_get(v_inst_3366_, 0);
        leanh::lean_inc_ref(v_toApplicative_3374_);
        leanh::lean_dec_ref(v_inst_3366_);
        v_toPure_3375_ = leanh::lean_ctor_get(v_toApplicative_3374_, 1);
        leanh::lean_inc(v_toPure_3375_);
        leanh::lean_dec_ref(v_toApplicative_3374_);
        v___x_3376_ =
            leanh::lean_apply_2(v_toPure_3375_, leanh::lean_box(0), v_init_3368_);
        return v___x_3376_;
    } else {
        let mut v___f_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3378_: u8 = 0;
        leanh::lean_inc_ref(v_inst_3366_);
        v___f_3377_ = leanh::lean_alloc_closure(
            l_Std_HashMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3377_, 0, v_inst_3366_);
        leanh::lean_closure_set(v___f_3377_, 1, v_f_3367_);
        v___x_3378_ = lean_nat_dec_le(v___x_3372_, v___x_3372_);
        if v___x_3378_ == 0 {
            if v___x_3373_ == 0 {
                let mut v_toApplicative_3379_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3377_);
                leanh::lean_dec_ref(v_buckets_3370_);
                v_toApplicative_3379_ = leanh::lean_ctor_get(v_inst_3366_, 0);
                leanh::lean_inc_ref(v_toApplicative_3379_);
                leanh::lean_dec_ref(v_inst_3366_);
                v_toPure_3380_ = leanh::lean_ctor_get(v_toApplicative_3379_, 1);
                leanh::lean_inc(v_toPure_3380_);
                leanh::lean_dec_ref(v_toApplicative_3379_);
                v___x_3381_ = leanh::lean_apply_2(
                    v_toPure_3380_,
                    leanh::lean_box(0),
                    v_init_3368_,
                );
                return v___x_3381_;
            } else {
                let mut v___x_3382_: usize = 0;
                let mut v___x_3383_: usize = 0;
                let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3382_ = 0usize;
                v___x_3383_ = lean_usize_of_nat(v___x_3372_);
                v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3366_,
                    v___f_3377_,
                    v_buckets_3370_,
                    v___x_3382_,
                    v___x_3383_,
                    v_init_3368_,
                );
                return v___x_3384_;
            }
        } else {
            let mut v___x_3385_: usize = 0;
            let mut v___x_3386_: usize = 0;
            let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3385_ = 0usize;
            v___x_3386_ = lean_usize_of_nat(v___x_3372_);
            v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3366_,
                v___f_3377_,
                v_buckets_3370_,
                v___x_3385_,
                v___x_3386_,
                v_init_3368_,
            );
            return v___x_3387_;
        }
    }
}
pub unsafe fn l_Std_HashMap_foldM(
    mut v_00_u03b1_3388_: *mut leanh::LeanObject,
    mut v_00_u03b2_3389_: *mut leanh::LeanObject,
    mut v_x_3390_: *mut leanh::LeanObject,
    mut v_x_3391_: *mut leanh::LeanObject,
    mut v_m_3392_: *mut leanh::LeanObject,
    mut v_inst_3393_: *mut leanh::LeanObject,
    mut v_00_u03b3_3394_: *mut leanh::LeanObject,
    mut v_f_3395_: *mut leanh::LeanObject,
    mut v_init_3396_: *mut leanh::LeanObject,
    mut v_b_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    v_buckets_3398_ = leanh::lean_ctor_get(v_b_3397_, 1);
    leanh::lean_inc_ref(v_buckets_3398_);
    leanh::lean_dec_ref(v_b_3397_);
    v___x_3399_ = leanh::lean_unsigned_to_nat(0);
    v___x_3400_ = lean_array_get_size(v_buckets_3398_);
    v___x_3401_ = lean_nat_dec_lt(v___x_3399_, v___x_3400_);
    if v___x_3401_ == 0 {
        let mut v_toApplicative_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3398_);
        leanh::lean_dec(v_f_3395_);
        v_toApplicative_3402_ = leanh::lean_ctor_get(v_inst_3393_, 0);
        leanh::lean_inc_ref(v_toApplicative_3402_);
        leanh::lean_dec_ref(v_inst_3393_);
        v_toPure_3403_ = leanh::lean_ctor_get(v_toApplicative_3402_, 1);
        leanh::lean_inc(v_toPure_3403_);
        leanh::lean_dec_ref(v_toApplicative_3402_);
        v___x_3404_ =
            leanh::lean_apply_2(v_toPure_3403_, leanh::lean_box(0), v_init_3396_);
        return v___x_3404_;
    } else {
        let mut v___f_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3406_: u8 = 0;
        leanh::lean_inc_ref(v_inst_3393_);
        v___f_3405_ = leanh::lean_alloc_closure(
            l_Std_HashMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3405_, 0, v_inst_3393_);
        leanh::lean_closure_set(v___f_3405_, 1, v_f_3395_);
        v___x_3406_ = lean_nat_dec_le(v___x_3400_, v___x_3400_);
        if v___x_3406_ == 0 {
            if v___x_3401_ == 0 {
                let mut v_toApplicative_3407_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3405_);
                leanh::lean_dec_ref(v_buckets_3398_);
                v_toApplicative_3407_ = leanh::lean_ctor_get(v_inst_3393_, 0);
                leanh::lean_inc_ref(v_toApplicative_3407_);
                leanh::lean_dec_ref(v_inst_3393_);
                v_toPure_3408_ = leanh::lean_ctor_get(v_toApplicative_3407_, 1);
                leanh::lean_inc(v_toPure_3408_);
                leanh::lean_dec_ref(v_toApplicative_3407_);
                v___x_3409_ = leanh::lean_apply_2(
                    v_toPure_3408_,
                    leanh::lean_box(0),
                    v_init_3396_,
                );
                return v___x_3409_;
            } else {
                let mut v___x_3410_: usize = 0;
                let mut v___x_3411_: usize = 0;
                let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3410_ = 0usize;
                v___x_3411_ = lean_usize_of_nat(v___x_3400_);
                v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3393_,
                    v___f_3405_,
                    v_buckets_3398_,
                    v___x_3410_,
                    v___x_3411_,
                    v_init_3396_,
                );
                return v___x_3412_;
            }
        } else {
            let mut v___x_3413_: usize = 0;
            let mut v___x_3414_: usize = 0;
            let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3413_ = 0usize;
            v___x_3414_ = lean_usize_of_nat(v___x_3400_);
            v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3393_,
                v___f_3405_,
                v_buckets_3398_,
                v___x_3413_,
                v___x_3414_,
                v_init_3396_,
            );
            return v___x_3415_;
        }
    }
}
pub unsafe fn l_Std_HashMap_foldM___boxed(
    mut v_00_u03b1_3416_: *mut leanh::LeanObject,
    mut v_00_u03b2_3417_: *mut leanh::LeanObject,
    mut v_x_3418_: *mut leanh::LeanObject,
    mut v_x_3419_: *mut leanh::LeanObject,
    mut v_m_3420_: *mut leanh::LeanObject,
    mut v_inst_3421_: *mut leanh::LeanObject,
    mut v_00_u03b3_3422_: *mut leanh::LeanObject,
    mut v_f_3423_: *mut leanh::LeanObject,
    mut v_init_3424_: *mut leanh::LeanObject,
    mut v_b_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Std_HashMap_foldM(
        v_00_u03b1_3416_,
        v_00_u03b2_3417_,
        v_x_3418_,
        v_x_3419_,
        v_m_3420_,
        v_inst_3421_,
        v_00_u03b3_3422_,
        v_f_3423_,
        v_init_3424_,
        v_b_3425_,
    );
    leanh::lean_dec_ref(v_x_3419_);
    leanh::lean_dec_ref(v_x_3418_);
    return v_res_3426_;
}
pub unsafe fn l_Std_HashMap_fold___redArg___lam__0(
    mut v_f_3427_: *mut leanh::LeanObject,
    mut v_x1_3428_: *mut leanh::LeanObject,
    mut v_x2_3429_: *mut leanh::LeanObject,
    mut v_x3_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = leanh::lean_apply_3(v_f_3427_, v_x1_3428_, v_x2_3429_, v_x3_3430_);
    return v___x_3431_;
}
pub unsafe fn l_Std_HashMap_fold___redArg___lam__1(
    mut v___x_3432_: *mut leanh::LeanObject,
    mut v___f_3433_: *mut leanh::LeanObject,
    mut v_acc_3434_: *mut leanh::LeanObject,
    mut v_l_3435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3436_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3432_,
        v___f_3433_,
        v_acc_3434_,
        v_l_3435_,
    );
    return v___x_3436_;
}
pub unsafe fn l_Std_HashMap_fold___redArg(
    mut v_f_3437_: *mut leanh::LeanObject,
    mut v_init_3438_: *mut leanh::LeanObject,
    mut v_b_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: u8 = 0;
    v___x_3440_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3441_ = leanh::lean_ctor_get(v_b_3439_, 1);
    leanh::lean_inc_ref(v_buckets_3441_);
    leanh::lean_dec_ref(v_b_3439_);
    v___x_3442_ = leanh::lean_unsigned_to_nat(0);
    v___x_3443_ = lean_array_get_size(v_buckets_3441_);
    v___x_3444_ = lean_nat_dec_lt(v___x_3442_, v___x_3443_);
    if v___x_3444_ == 0 {
        leanh::lean_dec_ref(v_buckets_3441_);
        leanh::lean_dec(v_f_3437_);
        return v_init_3438_;
    } else {
        let mut v___f_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3447_: u8 = 0;
        v___f_3445_ = leanh::lean_alloc_closure(
            l_Std_HashMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3445_, 0, v_f_3437_);
        v___f_3446_ = leanh::lean_alloc_closure(
            l_Std_HashMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3446_, 0, v___x_3440_);
        leanh::lean_closure_set(v___f_3446_, 1, v___f_3445_);
        v___x_3447_ = lean_nat_dec_le(v___x_3443_, v___x_3443_);
        if v___x_3447_ == 0 {
            if v___x_3444_ == 0 {
                leanh::lean_dec_ref(v___f_3446_);
                leanh::lean_dec_ref(v_buckets_3441_);
                return v_init_3438_;
            } else {
                let mut v___x_3448_: usize = 0;
                let mut v___x_3449_: usize = 0;
                let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3448_ = 0usize;
                v___x_3449_ = lean_usize_of_nat(v___x_3443_);
                v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3440_,
                    v___f_3446_,
                    v_buckets_3441_,
                    v___x_3448_,
                    v___x_3449_,
                    v_init_3438_,
                );
                return v___x_3450_;
            }
        } else {
            let mut v___x_3451_: usize = 0;
            let mut v___x_3452_: usize = 0;
            let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3451_ = 0usize;
            v___x_3452_ = lean_usize_of_nat(v___x_3443_);
            v___x_3453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3440_,
                v___f_3446_,
                v_buckets_3441_,
                v___x_3451_,
                v___x_3452_,
                v_init_3438_,
            );
            return v___x_3453_;
        }
    }
}
pub unsafe fn l_Std_HashMap_fold(
    mut v_00_u03b1_3454_: *mut leanh::LeanObject,
    mut v_00_u03b2_3455_: *mut leanh::LeanObject,
    mut v_x_3456_: *mut leanh::LeanObject,
    mut v_x_3457_: *mut leanh::LeanObject,
    mut v_00_u03b3_3458_: *mut leanh::LeanObject,
    mut v_f_3459_: *mut leanh::LeanObject,
    mut v_init_3460_: *mut leanh::LeanObject,
    mut v_b_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: u8 = 0;
    v___x_3462_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3463_ = leanh::lean_ctor_get(v_b_3461_, 1);
    leanh::lean_inc_ref(v_buckets_3463_);
    leanh::lean_dec_ref(v_b_3461_);
    v___x_3464_ = leanh::lean_unsigned_to_nat(0);
    v___x_3465_ = lean_array_get_size(v_buckets_3463_);
    v___x_3466_ = lean_nat_dec_lt(v___x_3464_, v___x_3465_);
    if v___x_3466_ == 0 {
        leanh::lean_dec_ref(v_buckets_3463_);
        leanh::lean_dec(v_f_3459_);
        return v_init_3460_;
    } else {
        let mut v___f_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3469_: u8 = 0;
        v___f_3467_ = leanh::lean_alloc_closure(
            l_Std_HashMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3467_, 0, v_f_3459_);
        v___f_3468_ = leanh::lean_alloc_closure(
            l_Std_HashMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3468_, 0, v___x_3462_);
        leanh::lean_closure_set(v___f_3468_, 1, v___f_3467_);
        v___x_3469_ = lean_nat_dec_le(v___x_3465_, v___x_3465_);
        if v___x_3469_ == 0 {
            if v___x_3466_ == 0 {
                leanh::lean_dec_ref(v___f_3468_);
                leanh::lean_dec_ref(v_buckets_3463_);
                return v_init_3460_;
            } else {
                let mut v___x_3470_: usize = 0;
                let mut v___x_3471_: usize = 0;
                let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3470_ = 0usize;
                v___x_3471_ = lean_usize_of_nat(v___x_3465_);
                v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3462_,
                    v___f_3468_,
                    v_buckets_3463_,
                    v___x_3470_,
                    v___x_3471_,
                    v_init_3460_,
                );
                return v___x_3472_;
            }
        } else {
            let mut v___x_3473_: usize = 0;
            let mut v___x_3474_: usize = 0;
            let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3473_ = 0usize;
            v___x_3474_ = lean_usize_of_nat(v___x_3465_);
            v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3462_,
                v___f_3468_,
                v_buckets_3463_,
                v___x_3473_,
                v___x_3474_,
                v_init_3460_,
            );
            return v___x_3475_;
        }
    }
}
pub unsafe fn l_Std_HashMap_fold___boxed(
    mut v_00_u03b1_3476_: *mut leanh::LeanObject,
    mut v_00_u03b2_3477_: *mut leanh::LeanObject,
    mut v_x_3478_: *mut leanh::LeanObject,
    mut v_x_3479_: *mut leanh::LeanObject,
    mut v_00_u03b3_3480_: *mut leanh::LeanObject,
    mut v_f_3481_: *mut leanh::LeanObject,
    mut v_init_3482_: *mut leanh::LeanObject,
    mut v_b_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l_Std_HashMap_fold(
        v_00_u03b1_3476_,
        v_00_u03b2_3477_,
        v_x_3478_,
        v_x_3479_,
        v_00_u03b3_3480_,
        v_f_3481_,
        v_init_3482_,
        v_b_3483_,
    );
    leanh::lean_dec_ref(v_x_3479_);
    leanh::lean_dec_ref(v_x_3478_);
    return v_res_3484_;
}
pub unsafe fn l_Std_HashMap_forM___redArg___lam__0(
    mut v_f_3485_: *mut leanh::LeanObject,
    mut v_x_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = leanh::lean_apply_2(v_f_3485_, v___y_3487_, v___y_3488_);
    return v___x_3489_;
}
pub unsafe fn l_Std_HashMap_forM___redArg___lam__1(
    mut v_inst_3490_: *mut leanh::LeanObject,
    mut v___f_3491_: *mut leanh::LeanObject,
    mut v_x_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = leanh::lean_box(0);
    v___x_3495_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_3490_,
        v___f_3491_,
        v___x_3494_,
        v___y_3493_,
    );
    return v___x_3495_;
}
pub unsafe fn l_Std_HashMap_forM___redArg(
    mut v_inst_3496_: *mut leanh::LeanObject,
    mut v_f_3497_: *mut leanh::LeanObject,
    mut v_b_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    v_buckets_3499_ = leanh::lean_ctor_get(v_b_3498_, 1);
    leanh::lean_inc_ref(v_buckets_3499_);
    leanh::lean_dec_ref(v_b_3498_);
    v___x_3500_ = leanh::lean_unsigned_to_nat(0);
    v___x_3501_ = lean_array_get_size(v_buckets_3499_);
    v___x_3502_ = leanh::lean_box(0);
    v___x_3503_ = lean_nat_dec_lt(v___x_3500_, v___x_3501_);
    if v___x_3503_ == 0 {
        let mut v_toApplicative_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3499_);
        leanh::lean_dec(v_f_3497_);
        v_toApplicative_3504_ = leanh::lean_ctor_get(v_inst_3496_, 0);
        leanh::lean_inc_ref(v_toApplicative_3504_);
        leanh::lean_dec_ref(v_inst_3496_);
        v_toPure_3505_ = leanh::lean_ctor_get(v_toApplicative_3504_, 1);
        leanh::lean_inc(v_toPure_3505_);
        leanh::lean_dec_ref(v_toApplicative_3504_);
        v___x_3506_ =
            leanh::lean_apply_2(v_toPure_3505_, leanh::lean_box(0), v___x_3502_);
        return v___x_3506_;
    } else {
        let mut v___f_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3509_: u8 = 0;
        v___f_3507_ = leanh::lean_alloc_closure(
            l_Std_HashMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3507_, 0, v_f_3497_);
        leanh::lean_inc_ref(v_inst_3496_);
        v___f_3508_ = leanh::lean_alloc_closure(
            l_Std_HashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3508_, 0, v_inst_3496_);
        leanh::lean_closure_set(v___f_3508_, 1, v___f_3507_);
        v___x_3509_ = lean_nat_dec_le(v___x_3501_, v___x_3501_);
        if v___x_3509_ == 0 {
            if v___x_3503_ == 0 {
                let mut v_toApplicative_3510_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3508_);
                leanh::lean_dec_ref(v_buckets_3499_);
                v_toApplicative_3510_ = leanh::lean_ctor_get(v_inst_3496_, 0);
                leanh::lean_inc_ref(v_toApplicative_3510_);
                leanh::lean_dec_ref(v_inst_3496_);
                v_toPure_3511_ = leanh::lean_ctor_get(v_toApplicative_3510_, 1);
                leanh::lean_inc(v_toPure_3511_);
                leanh::lean_dec_ref(v_toApplicative_3510_);
                v___x_3512_ = leanh::lean_apply_2(
                    v_toPure_3511_,
                    leanh::lean_box(0),
                    v___x_3502_,
                );
                return v___x_3512_;
            } else {
                let mut v___x_3513_: usize = 0;
                let mut v___x_3514_: usize = 0;
                let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3513_ = 0usize;
                v___x_3514_ = lean_usize_of_nat(v___x_3501_);
                v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3496_,
                    v___f_3508_,
                    v_buckets_3499_,
                    v___x_3513_,
                    v___x_3514_,
                    v___x_3502_,
                );
                return v___x_3515_;
            }
        } else {
            let mut v___x_3516_: usize = 0;
            let mut v___x_3517_: usize = 0;
            let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3516_ = 0usize;
            v___x_3517_ = lean_usize_of_nat(v___x_3501_);
            v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3496_,
                v___f_3508_,
                v_buckets_3499_,
                v___x_3516_,
                v___x_3517_,
                v___x_3502_,
            );
            return v___x_3518_;
        }
    }
}
pub unsafe fn l_Std_HashMap_forM(
    mut v_00_u03b1_3519_: *mut leanh::LeanObject,
    mut v_00_u03b2_3520_: *mut leanh::LeanObject,
    mut v_x_3521_: *mut leanh::LeanObject,
    mut v_x_3522_: *mut leanh::LeanObject,
    mut v_m_3523_: *mut leanh::LeanObject,
    mut v_inst_3524_: *mut leanh::LeanObject,
    mut v_f_3525_: *mut leanh::LeanObject,
    mut v_b_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    v_buckets_3527_ = leanh::lean_ctor_get(v_b_3526_, 1);
    leanh::lean_inc_ref(v_buckets_3527_);
    leanh::lean_dec_ref(v_b_3526_);
    v___x_3528_ = leanh::lean_unsigned_to_nat(0);
    v___x_3529_ = lean_array_get_size(v_buckets_3527_);
    v___x_3530_ = leanh::lean_box(0);
    v___x_3531_ = lean_nat_dec_lt(v___x_3528_, v___x_3529_);
    if v___x_3531_ == 0 {
        let mut v_toApplicative_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3527_);
        leanh::lean_dec(v_f_3525_);
        v_toApplicative_3532_ = leanh::lean_ctor_get(v_inst_3524_, 0);
        leanh::lean_inc_ref(v_toApplicative_3532_);
        leanh::lean_dec_ref(v_inst_3524_);
        v_toPure_3533_ = leanh::lean_ctor_get(v_toApplicative_3532_, 1);
        leanh::lean_inc(v_toPure_3533_);
        leanh::lean_dec_ref(v_toApplicative_3532_);
        v___x_3534_ =
            leanh::lean_apply_2(v_toPure_3533_, leanh::lean_box(0), v___x_3530_);
        return v___x_3534_;
    } else {
        let mut v___f_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3537_: u8 = 0;
        v___f_3535_ = leanh::lean_alloc_closure(
            l_Std_HashMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3535_, 0, v_f_3525_);
        leanh::lean_inc_ref(v_inst_3524_);
        v___f_3536_ = leanh::lean_alloc_closure(
            l_Std_HashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3536_, 0, v_inst_3524_);
        leanh::lean_closure_set(v___f_3536_, 1, v___f_3535_);
        v___x_3537_ = lean_nat_dec_le(v___x_3529_, v___x_3529_);
        if v___x_3537_ == 0 {
            if v___x_3531_ == 0 {
                let mut v_toApplicative_3538_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3536_);
                leanh::lean_dec_ref(v_buckets_3527_);
                v_toApplicative_3538_ = leanh::lean_ctor_get(v_inst_3524_, 0);
                leanh::lean_inc_ref(v_toApplicative_3538_);
                leanh::lean_dec_ref(v_inst_3524_);
                v_toPure_3539_ = leanh::lean_ctor_get(v_toApplicative_3538_, 1);
                leanh::lean_inc(v_toPure_3539_);
                leanh::lean_dec_ref(v_toApplicative_3538_);
                v___x_3540_ = leanh::lean_apply_2(
                    v_toPure_3539_,
                    leanh::lean_box(0),
                    v___x_3530_,
                );
                return v___x_3540_;
            } else {
                let mut v___x_3541_: usize = 0;
                let mut v___x_3542_: usize = 0;
                let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3541_ = 0usize;
                v___x_3542_ = lean_usize_of_nat(v___x_3529_);
                v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3524_,
                    v___f_3536_,
                    v_buckets_3527_,
                    v___x_3541_,
                    v___x_3542_,
                    v___x_3530_,
                );
                return v___x_3543_;
            }
        } else {
            let mut v___x_3544_: usize = 0;
            let mut v___x_3545_: usize = 0;
            let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3544_ = 0usize;
            v___x_3545_ = lean_usize_of_nat(v___x_3529_);
            v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3524_,
                v___f_3536_,
                v_buckets_3527_,
                v___x_3544_,
                v___x_3545_,
                v___x_3530_,
            );
            return v___x_3546_;
        }
    }
}
pub unsafe fn l_Std_HashMap_forM___boxed(
    mut v_00_u03b1_3547_: *mut leanh::LeanObject,
    mut v_00_u03b2_3548_: *mut leanh::LeanObject,
    mut v_x_3549_: *mut leanh::LeanObject,
    mut v_x_3550_: *mut leanh::LeanObject,
    mut v_m_3551_: *mut leanh::LeanObject,
    mut v_inst_3552_: *mut leanh::LeanObject,
    mut v_f_3553_: *mut leanh::LeanObject,
    mut v_b_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l_Std_HashMap_forM(
        v_00_u03b1_3547_,
        v_00_u03b2_3548_,
        v_x_3549_,
        v_x_3550_,
        v_m_3551_,
        v_inst_3552_,
        v_f_3553_,
        v_b_3554_,
    );
    leanh::lean_dec_ref(v_x_3550_);
    leanh::lean_dec_ref(v_x_3549_);
    return v_res_3555_;
}
pub unsafe fn l_Std_HashMap_forIn___redArg___lam__0(
    mut v_inst_3556_: *mut leanh::LeanObject,
    mut v_f_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_x_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_3556_, v_f_3557_, v_a_3558_, v___y_3560_);
    return v___x_3561_;
}
pub unsafe fn l_Std_HashMap_forIn___redArg(
    mut v_inst_3562_: *mut leanh::LeanObject,
    mut v_f_3563_: *mut leanh::LeanObject,
    mut v_init_3564_: *mut leanh::LeanObject,
    mut v_b_3565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3568_: usize = 0;
    let mut v___x_3569_: usize = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3566_ = leanh::lean_ctor_get(v_b_3565_, 1);
    leanh::lean_inc_ref(v_buckets_3566_);
    leanh::lean_dec_ref(v_b_3565_);
    leanh::lean_inc_ref(v_inst_3562_);
    v___f_3567_ = leanh::lean_alloc_closure(
        l_Std_HashMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3567_, 0, v_inst_3562_);
    leanh::lean_closure_set(v___f_3567_, 1, v_f_3563_);
    v_sz_3568_ = lean_array_size(v_buckets_3566_);
    v___x_3569_ = 0usize;
    v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3562_,
        v_buckets_3566_,
        v___f_3567_,
        v_sz_3568_,
        v___x_3569_,
        v_init_3564_,
    );
    return v___x_3570_;
}
pub unsafe fn l_Std_HashMap_forIn(
    mut v_00_u03b1_3571_: *mut leanh::LeanObject,
    mut v_00_u03b2_3572_: *mut leanh::LeanObject,
    mut v_x_3573_: *mut leanh::LeanObject,
    mut v_x_3574_: *mut leanh::LeanObject,
    mut v_m_3575_: *mut leanh::LeanObject,
    mut v_inst_3576_: *mut leanh::LeanObject,
    mut v_00_u03b3_3577_: *mut leanh::LeanObject,
    mut v_f_3578_: *mut leanh::LeanObject,
    mut v_init_3579_: *mut leanh::LeanObject,
    mut v_b_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3583_: usize = 0;
    let mut v___x_3584_: usize = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3581_ = leanh::lean_ctor_get(v_b_3580_, 1);
    leanh::lean_inc_ref(v_buckets_3581_);
    leanh::lean_dec_ref(v_b_3580_);
    leanh::lean_inc_ref(v_inst_3576_);
    v___f_3582_ = leanh::lean_alloc_closure(
        l_Std_HashMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3582_, 0, v_inst_3576_);
    leanh::lean_closure_set(v___f_3582_, 1, v_f_3578_);
    v_sz_3583_ = lean_array_size(v_buckets_3581_);
    v___x_3584_ = 0usize;
    v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3576_,
        v_buckets_3581_,
        v___f_3582_,
        v_sz_3583_,
        v___x_3584_,
        v_init_3579_,
    );
    return v___x_3585_;
}
pub unsafe fn l_Std_HashMap_forIn___boxed(
    mut v_00_u03b1_3586_: *mut leanh::LeanObject,
    mut v_00_u03b2_3587_: *mut leanh::LeanObject,
    mut v_x_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v_m_3590_: *mut leanh::LeanObject,
    mut v_inst_3591_: *mut leanh::LeanObject,
    mut v_00_u03b3_3592_: *mut leanh::LeanObject,
    mut v_f_3593_: *mut leanh::LeanObject,
    mut v_init_3594_: *mut leanh::LeanObject,
    mut v_b_3595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3596_ = l_Std_HashMap_forIn(
        v_00_u03b1_3586_,
        v_00_u03b2_3587_,
        v_x_3588_,
        v_x_3589_,
        v_m_3590_,
        v_inst_3591_,
        v_00_u03b3_3592_,
        v_f_3593_,
        v_init_3594_,
        v_b_3595_,
    );
    leanh::lean_dec_ref(v_x_3589_);
    leanh::lean_dec_ref(v_x_3588_);
    return v_res_3596_;
}
pub unsafe fn l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(
    mut v_f_3597_: *mut leanh::LeanObject,
    mut v_x_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v___y_3600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3601_, 0, v___y_3599_);
    leanh::lean_ctor_set(v___x_3601_, 1, v___y_3600_);
    v___x_3602_ = leanh::lean_apply_1(v_f_3597_, v___x_3601_);
    return v___x_3602_;
}
pub unsafe fn l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(
    mut v_inst_3603_: *mut leanh::LeanObject,
    mut v_m_3604_: *mut leanh::LeanObject,
    mut v_f_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    v_buckets_3606_ = leanh::lean_ctor_get(v_m_3604_, 1);
    leanh::lean_inc_ref(v_buckets_3606_);
    leanh::lean_dec_ref(v_m_3604_);
    v___x_3607_ = leanh::lean_unsigned_to_nat(0);
    v___x_3608_ = lean_array_get_size(v_buckets_3606_);
    v___x_3609_ = leanh::lean_box(0);
    v___x_3610_ = lean_nat_dec_lt(v___x_3607_, v___x_3608_);
    if v___x_3610_ == 0 {
        let mut v_toApplicative_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_3606_);
        leanh::lean_dec(v_f_3605_);
        v_toApplicative_3611_ = leanh::lean_ctor_get(v_inst_3603_, 0);
        leanh::lean_inc_ref(v_toApplicative_3611_);
        leanh::lean_dec_ref(v_inst_3603_);
        v_toPure_3612_ = leanh::lean_ctor_get(v_toApplicative_3611_, 1);
        leanh::lean_inc(v_toPure_3612_);
        leanh::lean_dec_ref(v_toApplicative_3611_);
        v___x_3613_ =
            leanh::lean_apply_2(v_toPure_3612_, leanh::lean_box(0), v___x_3609_);
        return v___x_3613_;
    } else {
        let mut v___f_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3616_: u8 = 0;
        v___f_3614_ = leanh::lean_alloc_closure(
            l_Std_HashMap_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_3614_, 0, v_f_3605_);
        leanh::lean_inc_ref(v_inst_3603_);
        v___f_3615_ = leanh::lean_alloc_closure(
            l_Std_HashMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_3615_, 0, v_inst_3603_);
        leanh::lean_closure_set(v___f_3615_, 1, v___f_3614_);
        v___x_3616_ = lean_nat_dec_le(v___x_3608_, v___x_3608_);
        if v___x_3616_ == 0 {
            if v___x_3610_ == 0 {
                let mut v_toApplicative_3617_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_3615_);
                leanh::lean_dec_ref(v_buckets_3606_);
                v_toApplicative_3617_ = leanh::lean_ctor_get(v_inst_3603_, 0);
                leanh::lean_inc_ref(v_toApplicative_3617_);
                leanh::lean_dec_ref(v_inst_3603_);
                v_toPure_3618_ = leanh::lean_ctor_get(v_toApplicative_3617_, 1);
                leanh::lean_inc(v_toPure_3618_);
                leanh::lean_dec_ref(v_toApplicative_3617_);
                v___x_3619_ = leanh::lean_apply_2(
                    v_toPure_3618_,
                    leanh::lean_box(0),
                    v___x_3609_,
                );
                return v___x_3619_;
            } else {
                let mut v___x_3620_: usize = 0;
                let mut v___x_3621_: usize = 0;
                let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3620_ = 0usize;
                v___x_3621_ = lean_usize_of_nat(v___x_3608_);
                v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3603_,
                    v___f_3615_,
                    v_buckets_3606_,
                    v___x_3620_,
                    v___x_3621_,
                    v___x_3609_,
                );
                return v___x_3622_;
            }
        } else {
            let mut v___x_3623_: usize = 0;
            let mut v___x_3624_: usize = 0;
            let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3623_ = 0usize;
            v___x_3624_ = lean_usize_of_nat(v___x_3608_);
            v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3603_,
                v___f_3615_,
                v_buckets_3606_,
                v___x_3623_,
                v___x_3624_,
                v___x_3609_,
            );
            return v___x_3625_;
        }
    }
}
pub unsafe fn l_Std_HashMap_instForMProdOfMonad___redArg(
    mut v_inst_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3627_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3627_, 0, v_inst_3626_);
    return v___f_3627_;
}
pub unsafe fn l_Std_HashMap_instForMProdOfMonad(
    mut v_00_u03b1_3628_: *mut leanh::LeanObject,
    mut v_00_u03b2_3629_: *mut leanh::LeanObject,
    mut v_inst_3630_: *mut leanh::LeanObject,
    mut v_inst_3631_: *mut leanh::LeanObject,
    mut v_m_3632_: *mut leanh::LeanObject,
    mut v_inst_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3634_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForMProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3634_, 0, v_inst_3633_);
    return v___f_3634_;
}
pub unsafe fn l_Std_HashMap_instForMProdOfMonad___boxed(
    mut v_00_u03b1_3635_: *mut leanh::LeanObject,
    mut v_00_u03b2_3636_: *mut leanh::LeanObject,
    mut v_inst_3637_: *mut leanh::LeanObject,
    mut v_inst_3638_: *mut leanh::LeanObject,
    mut v_m_3639_: *mut leanh::LeanObject,
    mut v_inst_3640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Std_HashMap_instForMProdOfMonad(
        v_00_u03b1_3635_,
        v_00_u03b2_3636_,
        v_inst_3637_,
        v_inst_3638_,
        v_m_3639_,
        v_inst_3640_,
    );
    leanh::lean_dec_ref(v_inst_3638_);
    leanh::lean_dec_ref(v_inst_3637_);
    return v_res_3641_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(
    mut v_f_3642_: *mut leanh::LeanObject,
    mut v_a_3643_: *mut leanh::LeanObject,
    mut v_b_3644_: *mut leanh::LeanObject,
    mut v_acc_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3646_, 0, v_a_3643_);
    leanh::lean_ctor_set(v___x_3646_, 1, v_b_3644_);
    v___x_3647_ = leanh::lean_apply_2(v_f_3642_, v___x_3646_, v_acc_3645_);
    return v___x_3647_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(
    mut v_inst_3648_: *mut leanh::LeanObject,
    mut v___f_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
    mut v_x_3651_: *mut leanh::LeanObject,
    mut v___y_3652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3653_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_inst_3648_, v___f_3649_, v_a_3650_, v___y_3652_);
    return v___x_3653_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(
    mut v_inst_3654_: *mut leanh::LeanObject,
    mut v_00_u03b2_3655_: *mut leanh::LeanObject,
    mut v_m_3656_: *mut leanh::LeanObject,
    mut v_init_3657_: *mut leanh::LeanObject,
    mut v_f_3658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3662_: usize = 0;
    let mut v___x_3663_: usize = 0;
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3659_ = leanh::lean_ctor_get(v_m_3656_, 1);
    leanh::lean_inc_ref(v_buckets_3659_);
    leanh::lean_dec_ref(v_m_3656_);
    v___f_3660_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3660_, 0, v_f_3658_);
    leanh::lean_inc_ref(v_inst_3654_);
    v___f_3661_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForInProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3661_, 0, v_inst_3654_);
    leanh::lean_closure_set(v___f_3661_, 1, v___f_3660_);
    v_sz_3662_ = lean_array_size(v_buckets_3659_);
    v___x_3663_ = 0usize;
    v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3654_,
        v_buckets_3659_,
        v___f_3661_,
        v_sz_3662_,
        v___x_3663_,
        v_init_3657_,
    );
    return v___x_3664_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad___redArg(
    mut v_inst_3665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3666_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3666_, 0, v_inst_3665_);
    return v___f_3666_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad(
    mut v_00_u03b1_3667_: *mut leanh::LeanObject,
    mut v_00_u03b2_3668_: *mut leanh::LeanObject,
    mut v_inst_3669_: *mut leanh::LeanObject,
    mut v_inst_3670_: *mut leanh::LeanObject,
    mut v_m_3671_: *mut leanh::LeanObject,
    mut v_inst_3672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3673_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3673_, 0, v_inst_3672_);
    return v___f_3673_;
}
pub unsafe fn l_Std_HashMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_3674_: *mut leanh::LeanObject,
    mut v_00_u03b2_3675_: *mut leanh::LeanObject,
    mut v_inst_3676_: *mut leanh::LeanObject,
    mut v_inst_3677_: *mut leanh::LeanObject,
    mut v_m_3678_: *mut leanh::LeanObject,
    mut v_inst_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_Std_HashMap_instForInProdOfMonad(
        v_00_u03b1_3674_,
        v_00_u03b2_3675_,
        v_inst_3676_,
        v_inst_3677_,
        v_m_3678_,
        v_inst_3679_,
    );
    leanh::lean_dec_ref(v_inst_3677_);
    leanh::lean_dec_ref(v_inst_3676_);
    return v_res_3680_;
}
pub unsafe fn l_Std_HashMap_filter___redArg(
    mut v_f_3681_: *mut leanh::LeanObject,
    mut v_m_3682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3683_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_3681_, v_m_3682_);
    return v___x_3683_;
}
pub unsafe fn l_Std_HashMap_filter(
    mut v_00_u03b1_3684_: *mut leanh::LeanObject,
    mut v_00_u03b2_3685_: *mut leanh::LeanObject,
    mut v_x_3686_: *mut leanh::LeanObject,
    mut v_x_3687_: *mut leanh::LeanObject,
    mut v_f_3688_: *mut leanh::LeanObject,
    mut v_m_3689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3690_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_3688_, v_m_3689_);
    return v___x_3690_;
}
pub unsafe fn l_Std_HashMap_filter___boxed(
    mut v_00_u03b1_3691_: *mut leanh::LeanObject,
    mut v_00_u03b2_3692_: *mut leanh::LeanObject,
    mut v_x_3693_: *mut leanh::LeanObject,
    mut v_x_3694_: *mut leanh::LeanObject,
    mut v_f_3695_: *mut leanh::LeanObject,
    mut v_m_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3697_ = l_Std_HashMap_filter(
        v_00_u03b1_3691_,
        v_00_u03b2_3692_,
        v_x_3693_,
        v_x_3694_,
        v_f_3695_,
        v_m_3696_,
    );
    leanh::lean_dec_ref(v_x_3694_);
    leanh::lean_dec_ref(v_x_3693_);
    return v_res_3697_;
}
pub unsafe fn l_Std_HashMap_modify___redArg(
    mut v_x_3698_: *mut leanh::LeanObject,
    mut v_x_3699_: *mut leanh::LeanObject,
    mut v_m_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
    mut v_f_3702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_3698_, v_x_3699_, v_m_3700_, v_a_3701_, v_f_3702_,
    );
    return v___x_3703_;
}
pub unsafe fn l_Std_HashMap_modify(
    mut v_00_u03b1_3704_: *mut leanh::LeanObject,
    mut v_00_u03b2_3705_: *mut leanh::LeanObject,
    mut v_x_3706_: *mut leanh::LeanObject,
    mut v_x_3707_: *mut leanh::LeanObject,
    mut v_m_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_f_3710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_x_3706_, v_x_3707_, v_m_3708_, v_a_3709_, v_f_3710_,
    );
    return v___x_3711_;
}
pub unsafe fn l_Std_HashMap_alter___redArg(
    mut v_x_3712_: *mut leanh::LeanObject,
    mut v_x_3713_: *mut leanh::LeanObject,
    mut v_m_3714_: *mut leanh::LeanObject,
    mut v_a_3715_: *mut leanh::LeanObject,
    mut v_f_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_3712_, v_x_3713_, v_m_3714_, v_a_3715_, v_f_3716_,
    );
    return v___x_3717_;
}
pub unsafe fn l_Std_HashMap_alter(
    mut v_00_u03b1_3718_: *mut leanh::LeanObject,
    mut v_00_u03b2_3719_: *mut leanh::LeanObject,
    mut v_x_3720_: *mut leanh::LeanObject,
    mut v_x_3721_: *mut leanh::LeanObject,
    mut v_m_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
    mut v_f_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_x_3720_, v_x_3721_, v_m_3722_, v_a_3723_, v_f_3724_,
    );
    return v___x_3725_;
}
pub unsafe fn l_Std_HashMap_insertMany___redArg(
    mut v_x_3726_: *mut leanh::LeanObject,
    mut v_x_3727_: *mut leanh::LeanObject,
    mut v_inst_3728_: *mut leanh::LeanObject,
    mut v_m_3729_: *mut leanh::LeanObject,
    mut v_l_3730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v_inst_3728_,
        v_x_3726_,
        v_x_3727_,
        v_m_3729_,
        v_l_3730_,
    );
    return v___x_3731_;
}
pub unsafe fn l_Std_HashMap_insertMany(
    mut v_00_u03b1_3732_: *mut leanh::LeanObject,
    mut v_00_u03b2_3733_: *mut leanh::LeanObject,
    mut v_x_3734_: *mut leanh::LeanObject,
    mut v_x_3735_: *mut leanh::LeanObject,
    mut v_00_u03c1_3736_: *mut leanh::LeanObject,
    mut v_inst_3737_: *mut leanh::LeanObject,
    mut v_m_3738_: *mut leanh::LeanObject,
    mut v_l_3739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v_inst_3737_,
        v_x_3734_,
        v_x_3735_,
        v_m_3738_,
        v_l_3739_,
    );
    return v___x_3740_;
}
pub unsafe fn l_Std_HashMap_insertManyIfNewUnit___redArg(
    mut v_x_3741_: *mut leanh::LeanObject,
    mut v_x_3742_: *mut leanh::LeanObject,
    mut v_inst_3743_: *mut leanh::LeanObject,
    mut v_m_3744_: *mut leanh::LeanObject,
    mut v_l_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_3743_,
        v_x_3741_,
        v_x_3742_,
        v_m_3744_,
        v_l_3745_,
    );
    return v___x_3746_;
}
pub unsafe fn l_Std_HashMap_insertManyIfNewUnit(
    mut v_00_u03b1_3747_: *mut leanh::LeanObject,
    mut v_x_3748_: *mut leanh::LeanObject,
    mut v_x_3749_: *mut leanh::LeanObject,
    mut v_00_u03c1_3750_: *mut leanh::LeanObject,
    mut v_inst_3751_: *mut leanh::LeanObject,
    mut v_m_3752_: *mut leanh::LeanObject,
    mut v_l_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_3751_,
        v_x_3748_,
        v_x_3749_,
        v_m_3752_,
        v_l_3753_,
    );
    return v___x_3754_;
}
pub unsafe fn l_Std_HashMap_toArray___redArg___lam__0(
    mut v_x1_3755_: *mut leanh::LeanObject,
    mut v_x2_3756_: *mut leanh::LeanObject,
    mut v_x3_3757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3758_, 0, v_x2_3756_);
    leanh::lean_ctor_set(v___x_3758_, 1, v_x3_3757_);
    v___x_3759_ = lean_array_push(v_x1_3755_, v___x_3758_);
    return v___x_3759_;
}
pub unsafe fn l_Std_HashMap_toArray___redArg___lam__1(
    mut v___x_3760_: *mut leanh::LeanObject,
    mut v___f_3761_: *mut leanh::LeanObject,
    mut v_acc_3762_: *mut leanh::LeanObject,
    mut v_l_3763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3764_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3760_,
        v___f_3761_,
        v_acc_3762_,
        v_l_3763_,
    );
    return v___x_3764_;
}
pub unsafe fn l_Std_HashMap_toArray___redArg(
    mut v_m_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    v_size_3770_ = leanh::lean_ctor_get(v_m_3769_, 0);
    leanh::lean_inc(v_size_3770_);
    v_buckets_3771_ = leanh::lean_ctor_get(v_m_3769_, 1);
    leanh::lean_inc_ref(v_buckets_3771_);
    leanh::lean_dec_ref(v_m_3769_);
    v___x_3772_ = lean_mk_empty_array_with_capacity(v_size_3770_);
    leanh::lean_dec(v_size_3770_);
    v___x_3773_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_3774_ = leanh::lean_unsigned_to_nat(0);
    v___x_3775_ = lean_array_get_size(v_buckets_3771_);
    v___x_3776_ = lean_nat_dec_lt(v___x_3774_, v___x_3775_);
    if v___x_3776_ == 0 {
        leanh::lean_dec_ref(v_buckets_3771_);
        return v___x_3772_;
    } else {
        let mut v___f_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3778_: u8 = 0;
        v___f_3777_ = l_Std_HashMap_toArray___redArg___closed__1;
        v___x_3778_ = lean_nat_dec_le(v___x_3775_, v___x_3775_);
        if v___x_3778_ == 0 {
            if v___x_3776_ == 0 {
                leanh::lean_dec_ref(v_buckets_3771_);
                return v___x_3772_;
            } else {
                let mut v___x_3779_: usize = 0;
                let mut v___x_3780_: usize = 0;
                let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3779_ = 0usize;
                v___x_3780_ = lean_usize_of_nat(v___x_3775_);
                v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3773_,
                    v___f_3777_,
                    v_buckets_3771_,
                    v___x_3779_,
                    v___x_3780_,
                    v___x_3772_,
                );
                return v___x_3781_;
            }
        } else {
            let mut v___x_3782_: usize = 0;
            let mut v___x_3783_: usize = 0;
            let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3782_ = 0usize;
            v___x_3783_ = lean_usize_of_nat(v___x_3775_);
            v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3773_,
                v___f_3777_,
                v_buckets_3771_,
                v___x_3782_,
                v___x_3783_,
                v___x_3772_,
            );
            return v___x_3784_;
        }
    }
}
pub unsafe fn l_Std_HashMap_toArray(
    mut v_00_u03b1_3785_: *mut leanh::LeanObject,
    mut v_00_u03b2_3786_: *mut leanh::LeanObject,
    mut v_x_3787_: *mut leanh::LeanObject,
    mut v_x_3788_: *mut leanh::LeanObject,
    mut v_m_3789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: u8 = 0;
    v_size_3790_ = leanh::lean_ctor_get(v_m_3789_, 0);
    leanh::lean_inc(v_size_3790_);
    v_buckets_3791_ = leanh::lean_ctor_get(v_m_3789_, 1);
    leanh::lean_inc_ref(v_buckets_3791_);
    leanh::lean_dec_ref(v_m_3789_);
    v___x_3792_ = lean_mk_empty_array_with_capacity(v_size_3790_);
    leanh::lean_dec(v_size_3790_);
    v___x_3793_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_3794_ = leanh::lean_unsigned_to_nat(0);
    v___x_3795_ = lean_array_get_size(v_buckets_3791_);
    v___x_3796_ = lean_nat_dec_lt(v___x_3794_, v___x_3795_);
    if v___x_3796_ == 0 {
        leanh::lean_dec_ref(v_buckets_3791_);
        return v___x_3792_;
    } else {
        let mut v___f_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3798_: u8 = 0;
        v___f_3797_ = l_Std_HashMap_toArray___redArg___closed__1;
        v___x_3798_ = lean_nat_dec_le(v___x_3795_, v___x_3795_);
        if v___x_3798_ == 0 {
            if v___x_3796_ == 0 {
                leanh::lean_dec_ref(v_buckets_3791_);
                return v___x_3792_;
            } else {
                let mut v___x_3799_: usize = 0;
                let mut v___x_3800_: usize = 0;
                let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3799_ = 0usize;
                v___x_3800_ = lean_usize_of_nat(v___x_3795_);
                v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3793_,
                    v___f_3797_,
                    v_buckets_3791_,
                    v___x_3799_,
                    v___x_3800_,
                    v___x_3792_,
                );
                return v___x_3801_;
            }
        } else {
            let mut v___x_3802_: usize = 0;
            let mut v___x_3803_: usize = 0;
            let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3802_ = 0usize;
            v___x_3803_ = lean_usize_of_nat(v___x_3795_);
            v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3793_,
                v___f_3797_,
                v_buckets_3791_,
                v___x_3802_,
                v___x_3803_,
                v___x_3792_,
            );
            return v___x_3804_;
        }
    }
}
pub unsafe fn l_Std_HashMap_toArray___boxed(
    mut v_00_u03b1_3805_: *mut leanh::LeanObject,
    mut v_00_u03b2_3806_: *mut leanh::LeanObject,
    mut v_x_3807_: *mut leanh::LeanObject,
    mut v_x_3808_: *mut leanh::LeanObject,
    mut v_m_3809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3810_ = l_Std_HashMap_toArray(
        v_00_u03b1_3805_,
        v_00_u03b2_3806_,
        v_x_3807_,
        v_x_3808_,
        v_m_3809_,
    );
    leanh::lean_dec_ref(v_x_3808_);
    leanh::lean_dec_ref(v_x_3807_);
    return v_res_3810_;
}
pub unsafe fn l_Std_HashMap_keysArray___redArg___lam__0(
    mut v_x1_3811_: *mut leanh::LeanObject,
    mut v_x2_3812_: *mut leanh::LeanObject,
    mut v_x3_3813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = lean_array_push(v_x1_3811_, v_x2_3812_);
    return v___x_3814_;
}
pub unsafe fn l_Std_HashMap_keysArray___redArg___lam__0___boxed(
    mut v_x1_3815_: *mut leanh::LeanObject,
    mut v_x2_3816_: *mut leanh::LeanObject,
    mut v_x3_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_3815_, v_x2_3816_, v_x3_3817_);
    leanh::lean_dec(v_x3_3817_);
    return v_res_3818_;
}
pub unsafe fn l_Std_HashMap_keysArray___redArg___lam__1(
    mut v___x_3819_: *mut leanh::LeanObject,
    mut v___f_3820_: *mut leanh::LeanObject,
    mut v_acc_3821_: *mut leanh::LeanObject,
    mut v_l_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3819_,
        v___f_3820_,
        v_acc_3821_,
        v_l_3822_,
    );
    return v___x_3823_;
}
pub unsafe fn l_Std_HashMap_keysArray___redArg(
    mut v_m_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    v_size_3829_ = leanh::lean_ctor_get(v_m_3828_, 0);
    leanh::lean_inc(v_size_3829_);
    v_buckets_3830_ = leanh::lean_ctor_get(v_m_3828_, 1);
    leanh::lean_inc_ref(v_buckets_3830_);
    leanh::lean_dec_ref(v_m_3828_);
    v___x_3831_ = lean_mk_empty_array_with_capacity(v_size_3829_);
    leanh::lean_dec(v_size_3829_);
    v___x_3832_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_3833_ = leanh::lean_unsigned_to_nat(0);
    v___x_3834_ = lean_array_get_size(v_buckets_3830_);
    v___x_3835_ = lean_nat_dec_lt(v___x_3833_, v___x_3834_);
    if v___x_3835_ == 0 {
        leanh::lean_dec_ref(v_buckets_3830_);
        return v___x_3831_;
    } else {
        let mut v___f_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3837_: u8 = 0;
        v___f_3836_ = l_Std_HashMap_keysArray___redArg___closed__1;
        v___x_3837_ = lean_nat_dec_le(v___x_3834_, v___x_3834_);
        if v___x_3837_ == 0 {
            if v___x_3835_ == 0 {
                leanh::lean_dec_ref(v_buckets_3830_);
                return v___x_3831_;
            } else {
                let mut v___x_3838_: usize = 0;
                let mut v___x_3839_: usize = 0;
                let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3838_ = 0usize;
                v___x_3839_ = lean_usize_of_nat(v___x_3834_);
                v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3832_,
                    v___f_3836_,
                    v_buckets_3830_,
                    v___x_3838_,
                    v___x_3839_,
                    v___x_3831_,
                );
                return v___x_3840_;
            }
        } else {
            let mut v___x_3841_: usize = 0;
            let mut v___x_3842_: usize = 0;
            let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3841_ = 0usize;
            v___x_3842_ = lean_usize_of_nat(v___x_3834_);
            v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3832_,
                v___f_3836_,
                v_buckets_3830_,
                v___x_3841_,
                v___x_3842_,
                v___x_3831_,
            );
            return v___x_3843_;
        }
    }
}
pub unsafe fn l_Std_HashMap_keysArray(
    mut v_00_u03b1_3844_: *mut leanh::LeanObject,
    mut v_00_u03b2_3845_: *mut leanh::LeanObject,
    mut v_x_3846_: *mut leanh::LeanObject,
    mut v_x_3847_: *mut leanh::LeanObject,
    mut v_m_3848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u8 = 0;
    v_size_3849_ = leanh::lean_ctor_get(v_m_3848_, 0);
    leanh::lean_inc(v_size_3849_);
    v_buckets_3850_ = leanh::lean_ctor_get(v_m_3848_, 1);
    leanh::lean_inc_ref(v_buckets_3850_);
    leanh::lean_dec_ref(v_m_3848_);
    v___x_3851_ = lean_mk_empty_array_with_capacity(v_size_3849_);
    leanh::lean_dec(v_size_3849_);
    v___x_3852_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_3853_ = leanh::lean_unsigned_to_nat(0);
    v___x_3854_ = lean_array_get_size(v_buckets_3850_);
    v___x_3855_ = lean_nat_dec_lt(v___x_3853_, v___x_3854_);
    if v___x_3855_ == 0 {
        leanh::lean_dec_ref(v_buckets_3850_);
        return v___x_3851_;
    } else {
        let mut v___f_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3857_: u8 = 0;
        v___f_3856_ = l_Std_HashMap_keysArray___redArg___closed__1;
        v___x_3857_ = lean_nat_dec_le(v___x_3854_, v___x_3854_);
        if v___x_3857_ == 0 {
            if v___x_3855_ == 0 {
                leanh::lean_dec_ref(v_buckets_3850_);
                return v___x_3851_;
            } else {
                let mut v___x_3858_: usize = 0;
                let mut v___x_3859_: usize = 0;
                let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3858_ = 0usize;
                v___x_3859_ = lean_usize_of_nat(v___x_3854_);
                v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3852_,
                    v___f_3856_,
                    v_buckets_3850_,
                    v___x_3858_,
                    v___x_3859_,
                    v___x_3851_,
                );
                return v___x_3860_;
            }
        } else {
            let mut v___x_3861_: usize = 0;
            let mut v___x_3862_: usize = 0;
            let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3861_ = 0usize;
            v___x_3862_ = lean_usize_of_nat(v___x_3854_);
            v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3852_,
                v___f_3856_,
                v_buckets_3850_,
                v___x_3861_,
                v___x_3862_,
                v___x_3851_,
            );
            return v___x_3863_;
        }
    }
}
pub unsafe fn l_Std_HashMap_keysArray___boxed(
    mut v_00_u03b1_3864_: *mut leanh::LeanObject,
    mut v_00_u03b2_3865_: *mut leanh::LeanObject,
    mut v_x_3866_: *mut leanh::LeanObject,
    mut v_x_3867_: *mut leanh::LeanObject,
    mut v_m_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Std_HashMap_keysArray(
        v_00_u03b1_3864_,
        v_00_u03b2_3865_,
        v_x_3866_,
        v_x_3867_,
        v_m_3868_,
    );
    leanh::lean_dec_ref(v_x_3867_);
    leanh::lean_dec_ref(v_x_3866_);
    return v_res_3869_;
}
pub unsafe fn l_Std_HashMap_all___redArg___lam__0(
    mut v_p_3870_: *mut leanh::LeanObject,
    mut v___x_3871_: *mut leanh::LeanObject,
    mut v___x_3872_: *mut leanh::LeanObject,
    mut v_a_3873_: *mut leanh::LeanObject,
    mut v_b_3874_: *mut leanh::LeanObject,
    mut v_acc_3875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    v___x_3876_ = leanh::lean_apply_2(v_p_3870_, v_a_3873_, v_b_3874_);
    v___x_3877_ = (leanh::lean_unbox(v___x_3876_) as u8);
    if v___x_3877_ == 0 {
        let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3872_);
        v___x_3878_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3878_, 0, v___x_3876_);
        v___x_3879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3879_, 0, v___x_3878_);
        leanh::lean_ctor_set(v___x_3879_, 1, v___x_3871_);
        v___x_3880_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3880_, 0, v___x_3879_);
        return v___x_3880_;
    } else {
        let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3881_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3881_, 0, v___x_3872_);
        return v___x_3881_;
    }
}
pub unsafe fn l_Std_HashMap_all___redArg___lam__0___boxed(
    mut v_p_3882_: *mut leanh::LeanObject,
    mut v___x_3883_: *mut leanh::LeanObject,
    mut v___x_3884_: *mut leanh::LeanObject,
    mut v_a_3885_: *mut leanh::LeanObject,
    mut v_b_3886_: *mut leanh::LeanObject,
    mut v_acc_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3888_ = l_Std_HashMap_all___redArg___lam__0(
        v_p_3882_,
        v___x_3883_,
        v___x_3884_,
        v_a_3885_,
        v_b_3886_,
        v_acc_3887_,
    );
    leanh::lean_dec_ref(v_acc_3887_);
    return v_res_3888_;
}
pub unsafe fn l_Std_HashMap_all___redArg___lam__1(
    mut v___x_3889_: *mut leanh::LeanObject,
    mut v___f_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_x_3892_: *mut leanh::LeanObject,
    mut v___y_3893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3894_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_3889_, v___f_3890_, v_a_3891_, v___y_3893_);
    return v___x_3894_;
}
pub unsafe fn l_Std_HashMap_all___redArg(
    mut v_m_3898_: *mut leanh::LeanObject,
    mut v_p_3899_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3906_: usize = 0;
    let mut v___x_3907_: usize = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3901_ = leanh::lean_ctor_get(v_m_3898_, 1);
    leanh::lean_inc_ref(v_buckets_3901_);
    leanh::lean_dec_ref(v_m_3898_);
    v___x_3902_ = leanh::lean_box(0);
    v___x_3903_ = l_Std_HashMap_all___redArg___closed__0;
    v___f_3904_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3904_, 0, v_p_3899_);
    leanh::lean_closure_set(v___f_3904_, 1, v___x_3902_);
    leanh::lean_closure_set(v___f_3904_, 2, v___x_3903_);
    v___f_3905_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3905_, 0, v___x_3900_);
    leanh::lean_closure_set(v___f_3905_, 1, v___f_3904_);
    v_sz_3906_ = lean_array_size(v_buckets_3901_);
    v___x_3907_ = 0usize;
    v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3900_,
        v_buckets_3901_,
        v___f_3905_,
        v_sz_3906_,
        v___x_3907_,
        v___x_3903_,
    );
    v_fst_3909_ = leanh::lean_ctor_get(v___x_3908_, 0);
    leanh::lean_inc(v_fst_3909_);
    leanh::lean_dec(v___x_3908_);
    if leanh::lean_obj_tag(v_fst_3909_) == 0 {
        let mut v___x_3910_: u8 = 0;
        v___x_3910_ = 1;
        return v___x_3910_;
    } else {
        let mut v_val_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3912_: u8 = 0;
        v_val_3911_ = leanh::lean_ctor_get(v_fst_3909_, 0);
        leanh::lean_inc(v_val_3911_);
        leanh::lean_dec_ref_known(v_fst_3909_, 1);
        v___x_3912_ = (leanh::lean_unbox(v_val_3911_) as u8);
        leanh::lean_dec(v_val_3911_);
        return v___x_3912_;
    }
}
pub unsafe fn l_Std_HashMap_all___redArg___boxed(
    mut v_m_3913_: *mut leanh::LeanObject,
    mut v_p_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3915_: u8 = 0;
    let mut v_r_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3915_ = l_Std_HashMap_all___redArg(v_m_3913_, v_p_3914_);
    v_r_3916_ = leanh::lean_box((v_res_3915_) as usize);
    return v_r_3916_;
}
pub unsafe fn l_Std_HashMap_all(
    mut v_00_u03b1_3917_: *mut leanh::LeanObject,
    mut v_00_u03b2_3918_: *mut leanh::LeanObject,
    mut v_x_3919_: *mut leanh::LeanObject,
    mut v_x_3920_: *mut leanh::LeanObject,
    mut v_m_3921_: *mut leanh::LeanObject,
    mut v_p_3922_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3929_: usize = 0;
    let mut v___x_3930_: usize = 0;
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3924_ = leanh::lean_ctor_get(v_m_3921_, 1);
    leanh::lean_inc_ref(v_buckets_3924_);
    leanh::lean_dec_ref(v_m_3921_);
    v___x_3925_ = leanh::lean_box(0);
    v___x_3926_ = l_Std_HashMap_all___redArg___closed__0;
    v___f_3927_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3927_, 0, v_p_3922_);
    leanh::lean_closure_set(v___f_3927_, 1, v___x_3925_);
    leanh::lean_closure_set(v___f_3927_, 2, v___x_3926_);
    v___f_3928_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3928_, 0, v___x_3923_);
    leanh::lean_closure_set(v___f_3928_, 1, v___f_3927_);
    v_sz_3929_ = lean_array_size(v_buckets_3924_);
    v___x_3930_ = 0usize;
    v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3923_,
        v_buckets_3924_,
        v___f_3928_,
        v_sz_3929_,
        v___x_3930_,
        v___x_3926_,
    );
    v_fst_3932_ = leanh::lean_ctor_get(v___x_3931_, 0);
    leanh::lean_inc(v_fst_3932_);
    leanh::lean_dec(v___x_3931_);
    if leanh::lean_obj_tag(v_fst_3932_) == 0 {
        let mut v___x_3933_: u8 = 0;
        v___x_3933_ = 1;
        return v___x_3933_;
    } else {
        let mut v_val_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3935_: u8 = 0;
        v_val_3934_ = leanh::lean_ctor_get(v_fst_3932_, 0);
        leanh::lean_inc(v_val_3934_);
        leanh::lean_dec_ref_known(v_fst_3932_, 1);
        v___x_3935_ = (leanh::lean_unbox(v_val_3934_) as u8);
        leanh::lean_dec(v_val_3934_);
        return v___x_3935_;
    }
}
pub unsafe fn l_Std_HashMap_all___boxed(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_00_u03b2_3937_: *mut leanh::LeanObject,
    mut v_x_3938_: *mut leanh::LeanObject,
    mut v_x_3939_: *mut leanh::LeanObject,
    mut v_m_3940_: *mut leanh::LeanObject,
    mut v_p_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3942_: u8 = 0;
    let mut v_r_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Std_HashMap_all(
        v_00_u03b1_3936_,
        v_00_u03b2_3937_,
        v_x_3938_,
        v_x_3939_,
        v_m_3940_,
        v_p_3941_,
    );
    leanh::lean_dec_ref(v_x_3939_);
    leanh::lean_dec_ref(v_x_3938_);
    v_r_3943_ = leanh::lean_box((v_res_3942_) as usize);
    return v_r_3943_;
}
pub unsafe fn l_Std_HashMap_any___redArg___lam__0(
    mut v_p_3944_: *mut leanh::LeanObject,
    mut v___x_3945_: *mut leanh::LeanObject,
    mut v___x_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
    mut v_b_3948_: *mut leanh::LeanObject,
    mut v_acc_3949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: u8 = 0;
    v___x_3950_ = leanh::lean_apply_2(v_p_3944_, v_a_3947_, v_b_3948_);
    v___x_3951_ = (leanh::lean_unbox(v___x_3950_) as u8);
    if v___x_3951_ == 0 {
        let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3952_, 0, v___x_3945_);
        return v___x_3952_;
    } else {
        let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_3945_);
        v___x_3953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3953_, 0, v___x_3950_);
        v___x_3954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3954_, 0, v___x_3953_);
        leanh::lean_ctor_set(v___x_3954_, 1, v___x_3946_);
        v___x_3955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3955_, 0, v___x_3954_);
        return v___x_3955_;
    }
}
pub unsafe fn l_Std_HashMap_any___redArg___lam__0___boxed(
    mut v_p_3956_: *mut leanh::LeanObject,
    mut v___x_3957_: *mut leanh::LeanObject,
    mut v___x_3958_: *mut leanh::LeanObject,
    mut v_a_3959_: *mut leanh::LeanObject,
    mut v_b_3960_: *mut leanh::LeanObject,
    mut v_acc_3961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3962_ = l_Std_HashMap_any___redArg___lam__0(
        v_p_3956_,
        v___x_3957_,
        v___x_3958_,
        v_a_3959_,
        v_b_3960_,
        v_acc_3961_,
    );
    leanh::lean_dec_ref(v_acc_3961_);
    return v_res_3962_;
}
pub unsafe fn l_Std_HashMap_any___redArg(
    mut v_m_3963_: *mut leanh::LeanObject,
    mut v_p_3964_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3971_: usize = 0;
    let mut v___x_3972_: usize = 0;
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3966_ = leanh::lean_ctor_get(v_m_3963_, 1);
    leanh::lean_inc_ref(v_buckets_3966_);
    leanh::lean_dec_ref(v_m_3963_);
    v___x_3967_ = leanh::lean_box(0);
    v___x_3968_ = l_Std_HashMap_all___redArg___closed__0;
    v___f_3969_ = leanh::lean_alloc_closure(
        l_Std_HashMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3969_, 0, v_p_3964_);
    leanh::lean_closure_set(v___f_3969_, 1, v___x_3968_);
    leanh::lean_closure_set(v___f_3969_, 2, v___x_3967_);
    v___f_3970_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3970_, 0, v___x_3965_);
    leanh::lean_closure_set(v___f_3970_, 1, v___f_3969_);
    v_sz_3971_ = lean_array_size(v_buckets_3966_);
    v___x_3972_ = 0usize;
    v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3965_,
        v_buckets_3966_,
        v___f_3970_,
        v_sz_3971_,
        v___x_3972_,
        v___x_3968_,
    );
    v_fst_3974_ = leanh::lean_ctor_get(v___x_3973_, 0);
    leanh::lean_inc(v_fst_3974_);
    leanh::lean_dec(v___x_3973_);
    if leanh::lean_obj_tag(v_fst_3974_) == 0 {
        let mut v___x_3975_: u8 = 0;
        v___x_3975_ = 0;
        return v___x_3975_;
    } else {
        let mut v_val_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3977_: u8 = 0;
        v_val_3976_ = leanh::lean_ctor_get(v_fst_3974_, 0);
        leanh::lean_inc(v_val_3976_);
        leanh::lean_dec_ref_known(v_fst_3974_, 1);
        v___x_3977_ = (leanh::lean_unbox(v_val_3976_) as u8);
        leanh::lean_dec(v_val_3976_);
        return v___x_3977_;
    }
}
pub unsafe fn l_Std_HashMap_any___redArg___boxed(
    mut v_m_3978_: *mut leanh::LeanObject,
    mut v_p_3979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3980_: u8 = 0;
    let mut v_r_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3980_ = l_Std_HashMap_any___redArg(v_m_3978_, v_p_3979_);
    v_r_3981_ = leanh::lean_box((v_res_3980_) as usize);
    return v_r_3981_;
}
pub unsafe fn l_Std_HashMap_any(
    mut v_00_u03b1_3982_: *mut leanh::LeanObject,
    mut v_00_u03b2_3983_: *mut leanh::LeanObject,
    mut v_x_3984_: *mut leanh::LeanObject,
    mut v_x_3985_: *mut leanh::LeanObject,
    mut v_m_3986_: *mut leanh::LeanObject,
    mut v_p_3987_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3994_: usize = 0;
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_3989_ = leanh::lean_ctor_get(v_m_3986_, 1);
    leanh::lean_inc_ref(v_buckets_3989_);
    leanh::lean_dec_ref(v_m_3986_);
    v___x_3990_ = leanh::lean_box(0);
    v___x_3991_ = l_Std_HashMap_all___redArg___closed__0;
    v___f_3992_ = leanh::lean_alloc_closure(
        l_Std_HashMap_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_3992_, 0, v_p_3987_);
    leanh::lean_closure_set(v___f_3992_, 1, v___x_3991_);
    leanh::lean_closure_set(v___f_3992_, 2, v___x_3990_);
    v___f_3993_ = leanh::lean_alloc_closure(
        l_Std_HashMap_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_3993_, 0, v___x_3988_);
    leanh::lean_closure_set(v___f_3993_, 1, v___f_3992_);
    v_sz_3994_ = lean_array_size(v_buckets_3989_);
    v___x_3995_ = 0usize;
    v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3988_,
        v_buckets_3989_,
        v___f_3993_,
        v_sz_3994_,
        v___x_3995_,
        v___x_3991_,
    );
    v_fst_3997_ = leanh::lean_ctor_get(v___x_3996_, 0);
    leanh::lean_inc(v_fst_3997_);
    leanh::lean_dec(v___x_3996_);
    if leanh::lean_obj_tag(v_fst_3997_) == 0 {
        let mut v___x_3998_: u8 = 0;
        v___x_3998_ = 0;
        return v___x_3998_;
    } else {
        let mut v_val_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4000_: u8 = 0;
        v_val_3999_ = leanh::lean_ctor_get(v_fst_3997_, 0);
        leanh::lean_inc(v_val_3999_);
        leanh::lean_dec_ref_known(v_fst_3997_, 1);
        v___x_4000_ = (leanh::lean_unbox(v_val_3999_) as u8);
        leanh::lean_dec(v_val_3999_);
        return v___x_4000_;
    }
}
pub unsafe fn l_Std_HashMap_any___boxed(
    mut v_00_u03b1_4001_: *mut leanh::LeanObject,
    mut v_00_u03b2_4002_: *mut leanh::LeanObject,
    mut v_x_4003_: *mut leanh::LeanObject,
    mut v_x_4004_: *mut leanh::LeanObject,
    mut v_m_4005_: *mut leanh::LeanObject,
    mut v_p_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4007_: u8 = 0;
    let mut v_r_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4007_ = l_Std_HashMap_any(
        v_00_u03b1_4001_,
        v_00_u03b2_4002_,
        v_x_4003_,
        v_x_4004_,
        v_m_4005_,
        v_p_4006_,
    );
    leanh::lean_dec_ref(v_x_4004_);
    leanh::lean_dec_ref(v_x_4003_);
    v_r_4008_ = leanh::lean_box((v_res_4007_) as usize);
    return v_r_4008_;
}
pub unsafe fn l_Std_HashMap_union___redArg___lam__0(
    mut v_inst_4009_: *mut leanh::LeanObject,
    mut v_inst_4010_: *mut leanh::LeanObject,
    mut v_a_4011_: *mut leanh::LeanObject,
    mut v_b_4012_: *mut leanh::LeanObject,
    mut v_acc_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_4014_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4009_,
        v_inst_4010_,
        v_acc_4013_,
        v_a_4011_,
        v_b_4012_,
    );
    v___x_4015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4015_, 0, v_r_4014_);
    return v___x_4015_;
}
pub unsafe fn l_Std_HashMap_union___redArg___lam__1(
    mut v___x_4016_: *mut leanh::LeanObject,
    mut v___f_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
    mut v_x_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_4016_, v___f_4017_, v_a_4018_, v___y_4020_);
    return v___x_4021_;
}
pub unsafe fn l_Std_HashMap_union___redArg(
    mut v_inst_4024_: *mut leanh::LeanObject,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_m_u2081_4026_: *mut leanh::LeanObject,
    mut v_m_u2082_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: u8 = 0;
    v_size_4028_ = leanh::lean_ctor_get(v_m_u2081_4026_, 0);
    v_buckets_4029_ = leanh::lean_ctor_get(v_m_u2081_4026_, 1);
    v_size_4030_ = leanh::lean_ctor_get(v_m_u2082_4027_, 0);
    v___x_4031_ = lean_nat_dec_le(v_size_4028_, v_size_4030_);
    if v___x_4031_ == 0 {
        let mut v___f_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4032_ = l_Std_HashMap_union___redArg___closed__0;
        v___x_4033_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_4032_,
            v_inst_4024_,
            v_inst_4025_,
            v_m_u2081_4026_,
            v_m_u2082_4027_,
        );
        return v___x_4033_;
    } else {
        let mut v___f_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4037_: usize = 0;
        let mut v___x_4038_: usize = 0;
        let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_4029_);
        leanh::lean_dec_ref(v_m_u2081_4026_);
        v___f_4034_ = leanh::lean_alloc_closure(
            l_Std_HashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4034_, 0, v_inst_4024_);
        leanh::lean_closure_set(v___f_4034_, 1, v_inst_4025_);
        v___x_4035_ = l_Std_HashMap_keys___redArg___closed__9;
        v___f_4036_ = leanh::lean_alloc_closure(
            l_Std_HashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4036_, 0, v___x_4035_);
        leanh::lean_closure_set(v___f_4036_, 1, v___f_4034_);
        v_sz_4037_ = lean_array_size(v_buckets_4029_);
        v___x_4038_ = 0usize;
        v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4035_,
            v_buckets_4029_,
            v___f_4036_,
            v_sz_4037_,
            v___x_4038_,
            v_m_u2082_4027_,
        );
        return v___x_4039_;
    }
}
pub unsafe fn l_Std_HashMap_union(
    mut v_00_u03b1_4040_: *mut leanh::LeanObject,
    mut v_00_u03b2_4041_: *mut leanh::LeanObject,
    mut v_inst_4042_: *mut leanh::LeanObject,
    mut v_inst_4043_: *mut leanh::LeanObject,
    mut v_m_u2081_4044_: *mut leanh::LeanObject,
    mut v_m_u2082_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    v_size_4046_ = leanh::lean_ctor_get(v_m_u2081_4044_, 0);
    v_buckets_4047_ = leanh::lean_ctor_get(v_m_u2081_4044_, 1);
    v_size_4048_ = leanh::lean_ctor_get(v_m_u2082_4045_, 0);
    v___x_4049_ = lean_nat_dec_le(v_size_4046_, v_size_4048_);
    if v___x_4049_ == 0 {
        let mut v___f_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4050_ = l_Std_HashMap_union___redArg___closed__0;
        v___x_4051_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_4050_,
            v_inst_4042_,
            v_inst_4043_,
            v_m_u2081_4044_,
            v_m_u2082_4045_,
        );
        return v___x_4051_;
    } else {
        let mut v___f_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4055_: usize = 0;
        let mut v___x_4056_: usize = 0;
        let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_4047_);
        leanh::lean_dec_ref(v_m_u2081_4044_);
        v___f_4052_ = leanh::lean_alloc_closure(
            l_Std_HashMap_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4052_, 0, v_inst_4042_);
        leanh::lean_closure_set(v___f_4052_, 1, v_inst_4043_);
        v___x_4053_ = l_Std_HashMap_keys___redArg___closed__9;
        v___f_4054_ = leanh::lean_alloc_closure(
            l_Std_HashMap_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4054_, 0, v___x_4053_);
        leanh::lean_closure_set(v___f_4054_, 1, v___f_4052_);
        v_sz_4055_ = lean_array_size(v_buckets_4047_);
        v___x_4056_ = 0usize;
        v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4053_,
            v_buckets_4047_,
            v___f_4054_,
            v_sz_4055_,
            v___x_4056_,
            v_m_u2082_4045_,
        );
        return v___x_4057_;
    }
}
pub unsafe fn l_Std_HashMap_instUnion___redArg(
    mut v_inst_4058_: *mut leanh::LeanObject,
    mut v_inst_4059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ =
        leanh::lean_alloc_closure(l_Std_HashMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4060_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4060_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4060_, 2, v_inst_4058_);
    leanh::lean_closure_set(v___x_4060_, 3, v_inst_4059_);
    return v___x_4060_;
}
pub unsafe fn l_Std_HashMap_instUnion(
    mut v_00_u03b1_4061_: *mut leanh::LeanObject,
    mut v_00_u03b2_4062_: *mut leanh::LeanObject,
    mut v_inst_4063_: *mut leanh::LeanObject,
    mut v_inst_4064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4065_ =
        leanh::lean_alloc_closure(l_Std_HashMap_union as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4065_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4065_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4065_, 2, v_inst_4063_);
    leanh::lean_closure_set(v___x_4065_, 3, v_inst_4064_);
    return v___x_4065_;
}
pub unsafe fn l_Std_HashMap_inter___redArg(
    mut v_inst_4066_: *mut leanh::LeanObject,
    mut v_inst_4067_: *mut leanh::LeanObject,
    mut v_m_u2081_4068_: *mut leanh::LeanObject,
    mut v_m_u2082_4069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4070_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_4066_,
        v_inst_4067_,
        v_m_u2081_4068_,
        v_m_u2082_4069_,
    );
    return v___x_4070_;
}
pub unsafe fn l_Std_HashMap_inter(
    mut v_00_u03b1_4071_: *mut leanh::LeanObject,
    mut v_00_u03b2_4072_: *mut leanh::LeanObject,
    mut v_inst_4073_: *mut leanh::LeanObject,
    mut v_inst_4074_: *mut leanh::LeanObject,
    mut v_m_u2081_4075_: *mut leanh::LeanObject,
    mut v_m_u2082_4076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4077_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_4073_,
        v_inst_4074_,
        v_m_u2081_4075_,
        v_m_u2082_4076_,
    );
    return v___x_4077_;
}
pub unsafe fn l_Std_HashMap_instInter___redArg(
    mut v_inst_4078_: *mut leanh::LeanObject,
    mut v_inst_4079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4080_ =
        leanh::lean_alloc_closure(l_Std_HashMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4080_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4080_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4080_, 2, v_inst_4078_);
    leanh::lean_closure_set(v___x_4080_, 3, v_inst_4079_);
    return v___x_4080_;
}
pub unsafe fn l_Std_HashMap_instInter(
    mut v_00_u03b1_4081_: *mut leanh::LeanObject,
    mut v_00_u03b2_4082_: *mut leanh::LeanObject,
    mut v_inst_4083_: *mut leanh::LeanObject,
    mut v_inst_4084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4085_ =
        leanh::lean_alloc_closure(l_Std_HashMap_inter as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4085_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4085_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4085_, 2, v_inst_4083_);
    leanh::lean_closure_set(v___x_4085_, 3, v_inst_4084_);
    return v___x_4085_;
}
pub unsafe fn l_Std_HashMap_beq___redArg(
    mut v_x_4086_: *mut leanh::LeanObject,
    mut v_inst_4087_: *mut leanh::LeanObject,
    mut v_inst_4088_: *mut leanh::LeanObject,
    mut v_m_u2081_4089_: *mut leanh::LeanObject,
    mut v_m_u2082_4090_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4091_: u8 = 0;
    v___x_4091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_4087_,
        v_x_4086_,
        v_inst_4088_,
        v_m_u2081_4089_,
        v_m_u2082_4090_,
    );
    return v___x_4091_;
}
pub unsafe fn l_Std_HashMap_beq___redArg___boxed(
    mut v_x_4092_: *mut leanh::LeanObject,
    mut v_inst_4093_: *mut leanh::LeanObject,
    mut v_inst_4094_: *mut leanh::LeanObject,
    mut v_m_u2081_4095_: *mut leanh::LeanObject,
    mut v_m_u2082_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4097_: u8 = 0;
    let mut v_r_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Std_HashMap_beq___redArg(
        v_x_4092_,
        v_inst_4093_,
        v_inst_4094_,
        v_m_u2081_4095_,
        v_m_u2082_4096_,
    );
    v_r_4098_ = leanh::lean_box((v_res_4097_) as usize);
    return v_r_4098_;
}
pub unsafe fn l_Std_HashMap_beq(
    mut v_00_u03b1_4099_: *mut leanh::LeanObject,
    mut v_x_4100_: *mut leanh::LeanObject,
    mut v_00_u03b2_4101_: *mut leanh::LeanObject,
    mut v_inst_4102_: *mut leanh::LeanObject,
    mut v_inst_4103_: *mut leanh::LeanObject,
    mut v_m_u2081_4104_: *mut leanh::LeanObject,
    mut v_m_u2082_4105_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4106_: u8 = 0;
    v___x_4106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_4102_,
        v_x_4100_,
        v_inst_4103_,
        v_m_u2081_4104_,
        v_m_u2082_4105_,
    );
    return v___x_4106_;
}
pub unsafe fn l_Std_HashMap_beq___boxed(
    mut v_00_u03b1_4107_: *mut leanh::LeanObject,
    mut v_x_4108_: *mut leanh::LeanObject,
    mut v_00_u03b2_4109_: *mut leanh::LeanObject,
    mut v_inst_4110_: *mut leanh::LeanObject,
    mut v_inst_4111_: *mut leanh::LeanObject,
    mut v_m_u2081_4112_: *mut leanh::LeanObject,
    mut v_m_u2082_4113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4114_: u8 = 0;
    let mut v_r_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4114_ = l_Std_HashMap_beq(
        v_00_u03b1_4107_,
        v_x_4108_,
        v_00_u03b2_4109_,
        v_inst_4110_,
        v_inst_4111_,
        v_m_u2081_4112_,
        v_m_u2082_4113_,
    );
    v_r_4115_ = leanh::lean_box((v_res_4114_) as usize);
    return v_r_4115_;
}
pub unsafe fn l_Std_HashMap_instBEq___redArg(
    mut v_x_4116_: *mut leanh::LeanObject,
    mut v_inst_4117_: *mut leanh::LeanObject,
    mut v_inst_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ =
        leanh::lean_alloc_closure(l_Std_HashMap_beq___boxed as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_4119_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4119_, 1, v_x_4116_);
    leanh::lean_closure_set(v___x_4119_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4119_, 3, v_inst_4117_);
    leanh::lean_closure_set(v___x_4119_, 4, v_inst_4118_);
    return v___x_4119_;
}
pub unsafe fn l_Std_HashMap_instBEq(
    mut v_00_u03b1_4120_: *mut leanh::LeanObject,
    mut v_00_u03b2_4121_: *mut leanh::LeanObject,
    mut v_x_4122_: *mut leanh::LeanObject,
    mut v_inst_4123_: *mut leanh::LeanObject,
    mut v_inst_4124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ =
        leanh::lean_alloc_closure(l_Std_HashMap_beq___boxed as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_4125_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4125_, 1, v_x_4122_);
    leanh::lean_closure_set(v___x_4125_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4125_, 3, v_inst_4123_);
    leanh::lean_closure_set(v___x_4125_, 4, v_inst_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Std_HashMap_diff___redArg___lam__0(
    mut v_inst_4126_: *mut leanh::LeanObject,
    mut v_inst_4127_: *mut leanh::LeanObject,
    mut v_m_u2082_4128_: *mut leanh::LeanObject,
    mut v___x_4129_: u8,
    mut v_k_4130_: *mut leanh::LeanObject,
    mut v_x_4131_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4132_: u8 = 0;
    v___x_4132_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_4126_,
        v_inst_4127_,
        v_m_u2082_4128_,
        v_k_4130_,
    );
    if v___x_4132_ == 0 {
        return v___x_4129_;
    } else {
        let mut v___x_4133_: u8 = 0;
        v___x_4133_ = 0;
        return v___x_4133_;
    }
}
pub unsafe fn l_Std_HashMap_diff___redArg___lam__0___boxed(
    mut v_inst_4134_: *mut leanh::LeanObject,
    mut v_inst_4135_: *mut leanh::LeanObject,
    mut v_m_u2082_4136_: *mut leanh::LeanObject,
    mut v___x_4137_: *mut leanh::LeanObject,
    mut v_k_4138_: *mut leanh::LeanObject,
    mut v_x_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_80__boxed_4140_: u8 = 0;
    let mut v_res_4141_: u8 = 0;
    let mut v_r_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_80__boxed_4140_ = (leanh::lean_unbox(v___x_4137_) as u8);
    v_res_4141_ = l_Std_HashMap_diff___redArg___lam__0(
        v_inst_4134_,
        v_inst_4135_,
        v_m_u2082_4136_,
        v___x_80__boxed_4140_,
        v_k_4138_,
        v_x_4139_,
    );
    leanh::lean_dec(v_x_4139_);
    leanh::lean_dec_ref(v_m_u2082_4136_);
    v_r_4142_ = leanh::lean_box((v_res_4141_) as usize);
    return v_r_4142_;
}
pub unsafe fn l_Std_HashMap_diff___redArg(
    mut v_inst_4143_: *mut leanh::LeanObject,
    mut v_inst_4144_: *mut leanh::LeanObject,
    mut v_m_u2081_4145_: *mut leanh::LeanObject,
    mut v_m_u2082_4146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    v_size_4147_ = leanh::lean_ctor_get(v_m_u2081_4145_, 0);
    v_size_4148_ = leanh::lean_ctor_get(v_m_u2082_4146_, 0);
    v___x_4149_ = lean_nat_dec_le(v_size_4147_, v_size_4148_);
    if v___x_4149_ == 0 {
        let mut v___f_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4150_ = l_Std_HashMap_union___redArg___closed__0;
        v___x_4151_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_4150_,
            v_inst_4143_,
            v_inst_4144_,
            v_m_u2081_4145_,
            v_m_u2082_4146_,
        );
        return v___x_4151_;
    } else {
        let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4152_ = leanh::lean_box((v___x_4149_) as usize);
        v___f_4153_ = leanh::lean_alloc_closure(
            l_Std_HashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_4153_, 0, v_inst_4143_);
        leanh::lean_closure_set(v___f_4153_, 1, v_inst_4144_);
        leanh::lean_closure_set(v___f_4153_, 2, v_m_u2082_4146_);
        leanh::lean_closure_set(v___f_4153_, 3, v___x_4152_);
        v___x_4154_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4153_, v_m_u2081_4145_);
        return v___x_4154_;
    }
}
pub unsafe fn l_Std_HashMap_diff(
    mut v_00_u03b1_4155_: *mut leanh::LeanObject,
    mut v_00_u03b2_4156_: *mut leanh::LeanObject,
    mut v_inst_4157_: *mut leanh::LeanObject,
    mut v_inst_4158_: *mut leanh::LeanObject,
    mut v_m_u2081_4159_: *mut leanh::LeanObject,
    mut v_m_u2082_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: u8 = 0;
    v_size_4161_ = leanh::lean_ctor_get(v_m_u2081_4159_, 0);
    v_size_4162_ = leanh::lean_ctor_get(v_m_u2082_4160_, 0);
    v___x_4163_ = lean_nat_dec_le(v_size_4161_, v_size_4162_);
    if v___x_4163_ == 0 {
        let mut v___f_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4164_ = l_Std_HashMap_union___redArg___closed__0;
        v___x_4165_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_4164_,
            v_inst_4157_,
            v_inst_4158_,
            v_m_u2081_4159_,
            v_m_u2082_4160_,
        );
        return v___x_4165_;
    } else {
        let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4166_ = leanh::lean_box((v___x_4163_) as usize);
        v___f_4167_ = leanh::lean_alloc_closure(
            l_Std_HashMap_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_4167_, 0, v_inst_4157_);
        leanh::lean_closure_set(v___f_4167_, 1, v_inst_4158_);
        leanh::lean_closure_set(v___f_4167_, 2, v_m_u2082_4160_);
        leanh::lean_closure_set(v___f_4167_, 3, v___x_4166_);
        v___x_4168_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4167_, v_m_u2081_4159_);
        return v___x_4168_;
    }
}
pub unsafe fn l_Std_HashMap_instSDiff___redArg(
    mut v_inst_4169_: *mut leanh::LeanObject,
    mut v_inst_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ =
        leanh::lean_alloc_closure(l_Std_HashMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4171_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4171_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4171_, 2, v_inst_4169_);
    leanh::lean_closure_set(v___x_4171_, 3, v_inst_4170_);
    return v___x_4171_;
}
pub unsafe fn l_Std_HashMap_instSDiff(
    mut v_00_u03b1_4172_: *mut leanh::LeanObject,
    mut v_00_u03b2_4173_: *mut leanh::LeanObject,
    mut v_inst_4174_: *mut leanh::LeanObject,
    mut v_inst_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ =
        leanh::lean_alloc_closure(l_Std_HashMap_diff as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4176_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4176_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4176_, 2, v_inst_4174_);
    leanh::lean_closure_set(v___x_4176_, 3, v_inst_4175_);
    return v___x_4176_;
}
pub unsafe fn l_Std_HashMap_partition___redArg___lam__0(
    mut v_f_4177_: *mut leanh::LeanObject,
    mut v_x_4178_: *mut leanh::LeanObject,
    mut v_x_4179_: *mut leanh::LeanObject,
    mut v_x1_4180_: *mut leanh::LeanObject,
    mut v_x2_4181_: *mut leanh::LeanObject,
    mut v_x3_4182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4183_ = leanh::lean_ctor_get(v_x1_4180_, 0);
                v_snd_4184_ = leanh::lean_ctor_get(v_x1_4180_, 1);
                v_isSharedCheck_4198_ = (!leanh::lean_is_exclusive(v_x1_4180_)) as u8;
                if v_isSharedCheck_4198_ == 0 {
                    v___x_4186_ = v_x1_4180_;
                    v_isShared_4187_ = v_isSharedCheck_4198_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4184_);
                    leanh::lean_inc(v_fst_4183_);
                    leanh::lean_dec(v_x1_4180_);
                    v___x_4186_ = leanh::lean_box(0);
                    v_isShared_4187_ = v_isSharedCheck_4198_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_x3_4182_);
                leanh::lean_inc(v_x2_4181_);
                v___x_4188_ = leanh::lean_apply_2(v_f_4177_, v_x2_4181_, v_x3_4182_);
                v___x_4189_ = (leanh::lean_unbox(v___x_4188_) as u8);
                if v___x_4189_ == 0 {
                    v___x_4190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_4178_,
                        v_x_4179_,
                        v_snd_4184_,
                        v_x2_4181_,
                        v_x3_4182_,
                    );
                    if v_isShared_4187_ == 0 {
                        leanh::lean_ctor_set(v___x_4186_, 1, v___x_4190_);
                        v___x_4192_ = v___x_4186_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_fst_4183_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 1, v___x_4190_);
                        v___x_4192_ = v_reuseFailAlloc_4193_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_x_4178_,
                        v_x_4179_,
                        v_fst_4183_,
                        v_x2_4181_,
                        v_x3_4182_,
                    );
                    if v_isShared_4187_ == 0 {
                        leanh::lean_ctor_set(v___x_4186_, 0, v___x_4194_);
                        v___x_4196_ = v___x_4186_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4197_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_snd_4184_);
                        v___x_4196_ = v_reuseFailAlloc_4197_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4192_;
            }
            3 => {
                return v___x_4196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_partition___redArg___lam__1(
    mut v___x_4199_: *mut leanh::LeanObject,
    mut v___f_4200_: *mut leanh::LeanObject,
    mut v_acc_4201_: *mut leanh::LeanObject,
    mut v_l_4202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4199_,
        v___f_4200_,
        v_acc_4201_,
        v_l_4202_,
    );
    return v___x_4203_;
}
pub unsafe fn _init_l_Std_HashMap_partition___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_4205_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    leanh::lean_ctor_set(v___x_4205_, 1, v___x_4204_);
    return v___x_4205_;
}
pub unsafe fn l_Std_HashMap_partition___redArg(
    mut v_x_4206_: *mut leanh::LeanObject,
    mut v_x_4207_: *mut leanh::LeanObject,
    mut v_f_4208_: *mut leanh::LeanObject,
    mut v_m_4209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___f_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: usize = 0;
    let mut v___x_4231_: usize = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: usize = 0;
    let mut v___x_4234_: usize = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = leanh::lean_unsigned_to_nat(0);
                v___x_4222_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_HashMap_partition___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Std_HashMap_partition___redArg___closed__0_once),
                    _init_l_Std_HashMap_partition___redArg___closed__0,
                );
                v___x_4223_ = l_Std_HashMap_keys___redArg___closed__9;
                v_buckets_4224_ = leanh::lean_ctor_get(v_m_4209_, 1);
                leanh::lean_inc_ref(v_buckets_4224_);
                leanh::lean_dec_ref(v_m_4209_);
                v___x_4225_ = lean_array_get_size(v_buckets_4224_);
                v___x_4226_ = lean_nat_dec_lt(v___x_4221_, v___x_4225_);
                if v___x_4226_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4224_);
                    leanh::lean_dec_ref(v_f_4208_);
                    leanh::lean_dec_ref(v_x_4207_);
                    leanh::lean_dec_ref(v_x_4206_);
                    return v___x_4222_;
                } else {
                    v___f_4227_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_4227_, 0, v_f_4208_);
                    leanh::lean_closure_set(v___f_4227_, 1, v_x_4206_);
                    leanh::lean_closure_set(v___f_4227_, 2, v_x_4207_);
                    v___f_4228_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_partition___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4228_, 0, v___x_4223_);
                    leanh::lean_closure_set(v___f_4228_, 1, v___f_4227_);
                    v___x_4229_ = lean_nat_dec_le(v___x_4225_, v___x_4225_);
                    if v___x_4229_ == 0 {
                        if v___x_4226_ == 0 {
                            leanh::lean_dec_ref(v___f_4228_);
                            leanh::lean_dec_ref(v_buckets_4224_);
                            return v___x_4222_;
                        } else {
                            v___x_4230_ = 0usize;
                            v___x_4231_ = lean_usize_of_nat(v___x_4225_);
                            v___x_4232_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_4223_,
                                    v___f_4228_,
                                    v_buckets_4224_,
                                    v___x_4230_,
                                    v___x_4231_,
                                    v___x_4222_,
                                );
                            v___y_4211_ = v___x_4232_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4233_ = 0usize;
                        v___x_4234_ = lean_usize_of_nat(v___x_4225_);
                        v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_4223_,
                            v___f_4228_,
                            v_buckets_4224_,
                            v___x_4233_,
                            v___x_4234_,
                            v___x_4222_,
                        );
                        v___y_4211_ = v___x_4235_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4212_ = leanh::lean_ctor_get(v___y_4211_, 0);
                v_snd_4213_ = leanh::lean_ctor_get(v___y_4211_, 1);
                v_isSharedCheck_4220_ = (!leanh::lean_is_exclusive(v___y_4211_)) as u8;
                if v_isSharedCheck_4220_ == 0 {
                    v___x_4215_ = v___y_4211_;
                    v_isShared_4216_ = v_isSharedCheck_4220_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4213_);
                    leanh::lean_inc(v_fst_4212_);
                    leanh::lean_dec(v___y_4211_);
                    v___x_4215_ = leanh::lean_box(0);
                    v_isShared_4216_ = v_isSharedCheck_4220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_fst_4212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_snd_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_partition(
    mut v_00_u03b1_4236_: *mut leanh::LeanObject,
    mut v_00_u03b2_4237_: *mut leanh::LeanObject,
    mut v_x_4238_: *mut leanh::LeanObject,
    mut v_x_4239_: *mut leanh::LeanObject,
    mut v_f_4240_: *mut leanh::LeanObject,
    mut v_m_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___f_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: u8 = 0;
    let mut v___x_4262_: usize = 0;
    let mut v___x_4263_: usize = 0;
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4253_ = leanh::lean_unsigned_to_nat(0);
                v___x_4254_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_HashMap_partition___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Std_HashMap_partition___redArg___closed__0_once),
                    _init_l_Std_HashMap_partition___redArg___closed__0,
                );
                v___x_4255_ = l_Std_HashMap_keys___redArg___closed__9;
                v_buckets_4256_ = leanh::lean_ctor_get(v_m_4241_, 1);
                leanh::lean_inc_ref(v_buckets_4256_);
                leanh::lean_dec_ref(v_m_4241_);
                v___x_4257_ = lean_array_get_size(v_buckets_4256_);
                v___x_4258_ = lean_nat_dec_lt(v___x_4253_, v___x_4257_);
                if v___x_4258_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4256_);
                    leanh::lean_dec_ref(v_f_4240_);
                    leanh::lean_dec_ref(v_x_4239_);
                    leanh::lean_dec_ref(v_x_4238_);
                    return v___x_4254_;
                } else {
                    v___f_4259_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_partition___redArg___lam__0 as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_4259_, 0, v_f_4240_);
                    leanh::lean_closure_set(v___f_4259_, 1, v_x_4238_);
                    leanh::lean_closure_set(v___f_4259_, 2, v_x_4239_);
                    v___f_4260_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_partition___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4260_, 0, v___x_4255_);
                    leanh::lean_closure_set(v___f_4260_, 1, v___f_4259_);
                    v___x_4261_ = lean_nat_dec_le(v___x_4257_, v___x_4257_);
                    if v___x_4261_ == 0 {
                        if v___x_4258_ == 0 {
                            leanh::lean_dec_ref(v___f_4260_);
                            leanh::lean_dec_ref(v_buckets_4256_);
                            return v___x_4254_;
                        } else {
                            v___x_4262_ = 0usize;
                            v___x_4263_ = lean_usize_of_nat(v___x_4257_);
                            v___x_4264_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_4255_,
                                    v___f_4260_,
                                    v_buckets_4256_,
                                    v___x_4262_,
                                    v___x_4263_,
                                    v___x_4254_,
                                );
                            v___y_4243_ = v___x_4264_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4265_ = 0usize;
                        v___x_4266_ = lean_usize_of_nat(v___x_4257_);
                        v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_4255_,
                            v___f_4260_,
                            v_buckets_4256_,
                            v___x_4265_,
                            v___x_4266_,
                            v___x_4254_,
                        );
                        v___y_4243_ = v___x_4267_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4244_ = leanh::lean_ctor_get(v___y_4243_, 0);
                v_snd_4245_ = leanh::lean_ctor_get(v___y_4243_, 1);
                v_isSharedCheck_4252_ = (!leanh::lean_is_exclusive(v___y_4243_)) as u8;
                if v_isSharedCheck_4252_ == 0 {
                    v___x_4247_ = v___y_4243_;
                    v_isShared_4248_ = v_isSharedCheck_4252_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4245_);
                    leanh::lean_inc(v_fst_4244_);
                    leanh::lean_dec(v___y_4243_);
                    v___x_4247_ = leanh::lean_box(0);
                    v_isShared_4248_ = v_isSharedCheck_4252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4248_ == 0 {
                    v___x_4250_ = v___x_4247_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_fst_4244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 1, v_snd_4245_);
                    v___x_4250_ = v_reuseFailAlloc_4251_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_values___redArg___lam__0(
    mut v_a_4268_: *mut leanh::LeanObject,
    mut v_b_4269_: *mut leanh::LeanObject,
    mut v_d_4270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4271_, 0, v_b_4269_);
    leanh::lean_ctor_set(v___x_4271_, 1, v_d_4270_);
    return v___x_4271_;
}
pub unsafe fn l_Std_HashMap_values___redArg___lam__0___boxed(
    mut v_a_4272_: *mut leanh::LeanObject,
    mut v_b_4273_: *mut leanh::LeanObject,
    mut v_d_4274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4275_ = l_Std_HashMap_values___redArg___lam__0(v_a_4272_, v_b_4273_, v_d_4274_);
    leanh::lean_dec(v_a_4272_);
    return v_res_4275_;
}
pub unsafe fn l_Std_HashMap_values___redArg(
    mut v_m_4280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: u8 = 0;
    v___x_4281_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_4282_ = leanh::lean_ctor_get(v_m_4280_, 1);
    leanh::lean_inc_ref(v_buckets_4282_);
    leanh::lean_dec_ref(v_m_4280_);
    v___x_4283_ = leanh::lean_box(0);
    v___x_4284_ = lean_array_get_size(v_buckets_4282_);
    v___x_4285_ = leanh::lean_unsigned_to_nat(0);
    v___x_4286_ = lean_nat_dec_lt(v___x_4285_, v___x_4284_);
    if v___x_4286_ == 0 {
        leanh::lean_dec_ref(v_buckets_4282_);
        return v___x_4283_;
    } else {
        let mut v___f_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4288_: usize = 0;
        let mut v___x_4289_: usize = 0;
        let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4287_ = l_Std_HashMap_values___redArg___closed__1;
        v___x_4288_ = lean_usize_of_nat(v___x_4284_);
        v___x_4289_ = 0usize;
        v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4281_,
            v___f_4287_,
            v_buckets_4282_,
            v___x_4288_,
            v___x_4289_,
            v___x_4283_,
        );
        return v___x_4290_;
    }
}
pub unsafe fn l_Std_HashMap_values(
    mut v_00_u03b1_4291_: *mut leanh::LeanObject,
    mut v_00_u03b2_4292_: *mut leanh::LeanObject,
    mut v_x_4293_: *mut leanh::LeanObject,
    mut v_x_4294_: *mut leanh::LeanObject,
    mut v_m_4295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    v___x_4296_ = l_Std_HashMap_keys___redArg___closed__9;
    v_buckets_4297_ = leanh::lean_ctor_get(v_m_4295_, 1);
    leanh::lean_inc_ref(v_buckets_4297_);
    leanh::lean_dec_ref(v_m_4295_);
    v___x_4298_ = leanh::lean_box(0);
    v___x_4299_ = lean_array_get_size(v_buckets_4297_);
    v___x_4300_ = leanh::lean_unsigned_to_nat(0);
    v___x_4301_ = lean_nat_dec_lt(v___x_4300_, v___x_4299_);
    if v___x_4301_ == 0 {
        leanh::lean_dec_ref(v_buckets_4297_);
        return v___x_4298_;
    } else {
        let mut v___f_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4303_: usize = 0;
        let mut v___x_4304_: usize = 0;
        let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4302_ = l_Std_HashMap_values___redArg___closed__1;
        v___x_4303_ = lean_usize_of_nat(v___x_4299_);
        v___x_4304_ = 0usize;
        v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4296_,
            v___f_4302_,
            v_buckets_4297_,
            v___x_4303_,
            v___x_4304_,
            v___x_4298_,
        );
        return v___x_4305_;
    }
}
pub unsafe fn l_Std_HashMap_values___boxed(
    mut v_00_u03b1_4306_: *mut leanh::LeanObject,
    mut v_00_u03b2_4307_: *mut leanh::LeanObject,
    mut v_x_4308_: *mut leanh::LeanObject,
    mut v_x_4309_: *mut leanh::LeanObject,
    mut v_m_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4311_ = l_Std_HashMap_values(
        v_00_u03b1_4306_,
        v_00_u03b2_4307_,
        v_x_4308_,
        v_x_4309_,
        v_m_4310_,
    );
    leanh::lean_dec_ref(v_x_4309_);
    leanh::lean_dec_ref(v_x_4308_);
    return v_res_4311_;
}
pub unsafe fn l_Std_HashMap_valuesArray___redArg___lam__0(
    mut v_x1_4312_: *mut leanh::LeanObject,
    mut v_x2_4313_: *mut leanh::LeanObject,
    mut v_x3_4314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4315_ = lean_array_push(v_x1_4312_, v_x3_4314_);
    return v___x_4315_;
}
pub unsafe fn l_Std_HashMap_valuesArray___redArg___lam__0___boxed(
    mut v_x1_4316_: *mut leanh::LeanObject,
    mut v_x2_4317_: *mut leanh::LeanObject,
    mut v_x3_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4319_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_4316_, v_x2_4317_, v_x3_4318_);
    leanh::lean_dec(v_x2_4317_);
    return v_res_4319_;
}
pub unsafe fn l_Std_HashMap_valuesArray___redArg(
    mut v_m_4324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: u8 = 0;
    v_size_4325_ = leanh::lean_ctor_get(v_m_4324_, 0);
    leanh::lean_inc(v_size_4325_);
    v_buckets_4326_ = leanh::lean_ctor_get(v_m_4324_, 1);
    leanh::lean_inc_ref(v_buckets_4326_);
    leanh::lean_dec_ref(v_m_4324_);
    v___x_4327_ = lean_mk_empty_array_with_capacity(v_size_4325_);
    leanh::lean_dec(v_size_4325_);
    v___x_4328_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_4329_ = leanh::lean_unsigned_to_nat(0);
    v___x_4330_ = lean_array_get_size(v_buckets_4326_);
    v___x_4331_ = lean_nat_dec_lt(v___x_4329_, v___x_4330_);
    if v___x_4331_ == 0 {
        leanh::lean_dec_ref(v_buckets_4326_);
        return v___x_4327_;
    } else {
        let mut v___f_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: u8 = 0;
        v___f_4332_ = l_Std_HashMap_valuesArray___redArg___closed__1;
        v___x_4333_ = lean_nat_dec_le(v___x_4330_, v___x_4330_);
        if v___x_4333_ == 0 {
            if v___x_4331_ == 0 {
                leanh::lean_dec_ref(v_buckets_4326_);
                return v___x_4327_;
            } else {
                let mut v___x_4334_: usize = 0;
                let mut v___x_4335_: usize = 0;
                let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4334_ = 0usize;
                v___x_4335_ = lean_usize_of_nat(v___x_4330_);
                v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4328_,
                    v___f_4332_,
                    v_buckets_4326_,
                    v___x_4334_,
                    v___x_4335_,
                    v___x_4327_,
                );
                return v___x_4336_;
            }
        } else {
            let mut v___x_4337_: usize = 0;
            let mut v___x_4338_: usize = 0;
            let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4337_ = 0usize;
            v___x_4338_ = lean_usize_of_nat(v___x_4330_);
            v___x_4339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4328_,
                v___f_4332_,
                v_buckets_4326_,
                v___x_4337_,
                v___x_4338_,
                v___x_4327_,
            );
            return v___x_4339_;
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesArray(
    mut v_00_u03b1_4340_: *mut leanh::LeanObject,
    mut v_00_u03b2_4341_: *mut leanh::LeanObject,
    mut v_x_4342_: *mut leanh::LeanObject,
    mut v_x_4343_: *mut leanh::LeanObject,
    mut v_m_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: u8 = 0;
    v_size_4345_ = leanh::lean_ctor_get(v_m_4344_, 0);
    leanh::lean_inc(v_size_4345_);
    v_buckets_4346_ = leanh::lean_ctor_get(v_m_4344_, 1);
    leanh::lean_inc_ref(v_buckets_4346_);
    leanh::lean_dec_ref(v_m_4344_);
    v___x_4347_ = lean_mk_empty_array_with_capacity(v_size_4345_);
    leanh::lean_dec(v_size_4345_);
    v___x_4348_ = l_Std_HashMap_keys___redArg___closed__9;
    v___x_4349_ = leanh::lean_unsigned_to_nat(0);
    v___x_4350_ = lean_array_get_size(v_buckets_4346_);
    v___x_4351_ = lean_nat_dec_lt(v___x_4349_, v___x_4350_);
    if v___x_4351_ == 0 {
        leanh::lean_dec_ref(v_buckets_4346_);
        return v___x_4347_;
    } else {
        let mut v___f_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4353_: u8 = 0;
        v___f_4352_ = l_Std_HashMap_valuesArray___redArg___closed__1;
        v___x_4353_ = lean_nat_dec_le(v___x_4350_, v___x_4350_);
        if v___x_4353_ == 0 {
            if v___x_4351_ == 0 {
                leanh::lean_dec_ref(v_buckets_4346_);
                return v___x_4347_;
            } else {
                let mut v___x_4354_: usize = 0;
                let mut v___x_4355_: usize = 0;
                let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4354_ = 0usize;
                v___x_4355_ = lean_usize_of_nat(v___x_4350_);
                v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4348_,
                    v___f_4352_,
                    v_buckets_4346_,
                    v___x_4354_,
                    v___x_4355_,
                    v___x_4347_,
                );
                return v___x_4356_;
            }
        } else {
            let mut v___x_4357_: usize = 0;
            let mut v___x_4358_: usize = 0;
            let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4357_ = 0usize;
            v___x_4358_ = lean_usize_of_nat(v___x_4350_);
            v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4348_,
                v___f_4352_,
                v_buckets_4346_,
                v___x_4357_,
                v___x_4358_,
                v___x_4347_,
            );
            return v___x_4359_;
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesArray___boxed(
    mut v_00_u03b1_4360_: *mut leanh::LeanObject,
    mut v_00_u03b2_4361_: *mut leanh::LeanObject,
    mut v_x_4362_: *mut leanh::LeanObject,
    mut v_x_4363_: *mut leanh::LeanObject,
    mut v_m_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Std_HashMap_valuesArray(
        v_00_u03b1_4360_,
        v_00_u03b2_4361_,
        v_x_4362_,
        v_x_4363_,
        v_m_4364_,
    );
    leanh::lean_dec_ref(v_x_4363_);
    leanh::lean_dec_ref(v_x_4362_);
    return v_res_4365_;
}
pub unsafe fn l_Std_HashMap_unitOfArray___redArg(
    mut v_inst_4366_: *mut leanh::LeanObject,
    mut v_inst_4367_: *mut leanh::LeanObject,
    mut v_l_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4369_ = l_Std_HashMap_ofArray___redArg___closed__1;
    v___x_4370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_4371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_4369_,
        v_inst_4366_,
        v_inst_4367_,
        v___x_4370_,
        v_l_4368_,
    );
    return v___x_4371_;
}
pub unsafe fn l_Std_HashMap_unitOfArray(
    mut v_00_u03b1_4372_: *mut leanh::LeanObject,
    mut v_inst_4373_: *mut leanh::LeanObject,
    mut v_inst_4374_: *mut leanh::LeanObject,
    mut v_l_4375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4376_ = l_Std_HashMap_ofArray___redArg___closed__1;
    v___x_4377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_4378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_4376_,
        v_inst_4373_,
        v_inst_4374_,
        v___x_4377_,
        v_l_4375_,
    );
    return v___x_4378_;
}
pub unsafe fn l_Std_HashMap_Internal_numBuckets___redArg(
    mut v_m_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4379_);
    return v___x_4380_;
}
pub unsafe fn l_Std_HashMap_Internal_numBuckets___redArg___boxed(
    mut v_m_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4382_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_4381_);
    leanh::lean_dec_ref(v_m_4381_);
    return v_res_4382_;
}
pub unsafe fn l_Std_HashMap_Internal_numBuckets(
    mut v_00_u03b1_4383_: *mut leanh::LeanObject,
    mut v_00_u03b2_4384_: *mut leanh::LeanObject,
    mut v_x_4385_: *mut leanh::LeanObject,
    mut v_x_4386_: *mut leanh::LeanObject,
    mut v_m_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4388_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_4387_);
    return v___x_4388_;
}
pub unsafe fn l_Std_HashMap_Internal_numBuckets___boxed(
    mut v_00_u03b1_4389_: *mut leanh::LeanObject,
    mut v_00_u03b2_4390_: *mut leanh::LeanObject,
    mut v_x_4391_: *mut leanh::LeanObject,
    mut v_x_4392_: *mut leanh::LeanObject,
    mut v_m_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Std_HashMap_Internal_numBuckets(
        v_00_u03b1_4389_,
        v_00_u03b2_4390_,
        v_x_4391_,
        v_x_4392_,
        v_m_4393_,
    );
    leanh::lean_dec_ref(v_m_4393_);
    leanh::lean_dec_ref(v_x_4392_);
    leanh::lean_dec_ref(v_x_4391_);
    return v_res_4394_;
}
pub unsafe fn l_Std_HashMap_instRepr___redArg___lam__2(
    mut v___x_4398_: *mut leanh::LeanObject,
    mut v___f_4399_: *mut leanh::LeanObject,
    mut v_m_4400_: *mut leanh::LeanObject,
    mut v_prec_4401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4406_: u8 = 0;
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___f_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: usize = 0;
    let mut v___x_4421_: usize = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v_unused_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4402_ = l_Std_HashMap_keys___redArg___closed__9;
                v_buckets_4403_ = leanh::lean_ctor_get(v_m_4400_, 1);
                v_isSharedCheck_4423_ = (!leanh::lean_is_exclusive(v_m_4400_)) as u8;
                if v_isSharedCheck_4423_ == 0 {
                    v_unused_4424_ = leanh::lean_ctor_get(v_m_4400_, 0);
                    leanh::lean_dec(v_unused_4424_);
                    v___x_4405_ = v_m_4400_;
                    v_isShared_4406_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4403_);
                    leanh::lean_dec(v_m_4400_);
                    v___x_4405_ = leanh::lean_box(0);
                    v_isShared_4406_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4407_ = l_Std_HashMap_instRepr___redArg___lam__2___closed__1;
                v___x_4415_ = leanh::lean_box(0);
                v___x_4416_ = lean_array_get_size(v_buckets_4403_);
                v___x_4417_ = leanh::lean_unsigned_to_nat(0);
                v___x_4418_ = lean_nat_dec_lt(v___x_4417_, v___x_4416_);
                if v___x_4418_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4403_);
                    leanh::lean_dec_ref(v___f_4399_);
                    v___y_4409_ = v___x_4415_;
                    state = 2;
                    continue;
                } else {
                    v___f_4419_ = leanh::lean_alloc_closure(
                        l_Std_HashMap_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4419_, 0, v___x_4402_);
                    leanh::lean_closure_set(v___f_4419_, 1, v___f_4399_);
                    v___x_4420_ = lean_usize_of_nat(v___x_4416_);
                    v___x_4421_ = 0usize;
                    v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_4402_,
                        v___f_4419_,
                        v_buckets_4403_,
                        v___x_4420_,
                        v___x_4421_,
                        v___x_4415_,
                    );
                    v___y_4409_ = v___x_4422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4410_ = l_List_repr___redArg(v___x_4398_, v___y_4409_);
                if v_isShared_4406_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4405_, 5);
                    leanh::lean_ctor_set(v___x_4405_, 1, v___x_4410_);
                    leanh::lean_ctor_set(v___x_4405_, 0, v___x_4407_);
                    v___x_4412_ = v___x_4405_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 1, v___x_4410_);
                    v___x_4412_ = v_reuseFailAlloc_4414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4413_ = l_Repr_addAppParen(v___x_4412_, v_prec_4401_);
                return v___x_4413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_instRepr___redArg___lam__2___boxed(
    mut v___x_4425_: *mut leanh::LeanObject,
    mut v___f_4426_: *mut leanh::LeanObject,
    mut v_m_4427_: *mut leanh::LeanObject,
    mut v_prec_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ =
        l_Std_HashMap_instRepr___redArg___lam__2(v___x_4425_, v___f_4426_, v_m_4427_, v_prec_4428_);
    leanh::lean_dec(v_prec_4428_);
    return v_res_4429_;
}
pub unsafe fn l_Std_HashMap_instRepr___redArg(
    mut v_inst_4430_: *mut leanh::LeanObject,
    mut v_inst_4431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4432_ = l_Std_HashMap_toList___redArg___closed__0;
    v___f_4433_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4433_, 0, v_inst_4431_);
    v___x_4434_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_4434_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4434_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4434_, 2, v_inst_4430_);
    leanh::lean_closure_set(v___x_4434_, 3, v___f_4433_);
    v___f_4435_ = leanh::lean_alloc_closure(
        l_Std_HashMap_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4435_, 0, v___x_4434_);
    leanh::lean_closure_set(v___f_4435_, 1, v___f_4432_);
    return v___f_4435_;
}
pub unsafe fn l_Std_HashMap_instRepr(
    mut v_00_u03b1_4436_: *mut leanh::LeanObject,
    mut v_00_u03b2_4437_: *mut leanh::LeanObject,
    mut v_inst_4438_: *mut leanh::LeanObject,
    mut v_inst_4439_: *mut leanh::LeanObject,
    mut v_inst_4440_: *mut leanh::LeanObject,
    mut v_inst_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Std_HashMap_instRepr___redArg(v_inst_4440_, v_inst_4441_);
    return v___x_4442_;
}
pub unsafe fn l_Std_HashMap_instRepr___boxed(
    mut v_00_u03b1_4443_: *mut leanh::LeanObject,
    mut v_00_u03b2_4444_: *mut leanh::LeanObject,
    mut v_inst_4445_: *mut leanh::LeanObject,
    mut v_inst_4446_: *mut leanh::LeanObject,
    mut v_inst_4447_: *mut leanh::LeanObject,
    mut v_inst_4448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Std_HashMap_instRepr(
        v_00_u03b1_4443_,
        v_00_u03b2_4444_,
        v_inst_4445_,
        v_inst_4446_,
        v_inst_4447_,
        v_inst_4448_,
    );
    leanh::lean_dec_ref(v_inst_4446_);
    leanh::lean_dec_ref(v_inst_4445_);
    return v_res_4449_;
}
pub unsafe fn l_Array_groupByKey___redArg___lam__0(
    mut v_a_4452_: *mut leanh::LeanObject,
    mut v_x_4453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4453_) == 0 {
                    v___x_4458_ = l_Array_groupByKey___redArg___lam__0___closed__0;
                    v___y_4455_ = v___x_4458_;
                    state = 1;
                    continue;
                } else {
                    v_val_4459_ = leanh::lean_ctor_get(v_x_4453_, 0);
                    leanh::lean_inc(v_val_4459_);
                    leanh::lean_dec_ref_known(v_x_4453_, 1);
                    v___y_4455_ = v_val_4459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4456_ = lean_array_push(v___y_4455_, v_a_4452_);
                v___x_4457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4457_, 0, v___x_4456_);
                return v___x_4457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_groupByKey___redArg___lam__1(
    mut v_key_4460_: *mut leanh::LeanObject,
    mut v_inst_4461_: *mut leanh::LeanObject,
    mut v_inst_4462_: *mut leanh::LeanObject,
    mut v_a_4463_: *mut leanh::LeanObject,
    mut v_x_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_4463_);
    v___f_4466_ = leanh::lean_alloc_closure(
        l_Array_groupByKey___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4466_, 0, v_a_4463_);
    v___x_4467_ = leanh::lean_apply_1(v_key_4460_, v_a_4463_);
    v___x_4468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_inst_4461_,
        v_inst_4462_,
        v___y_4465_,
        v___x_4467_,
        v___f_4466_,
    );
    v___x_4469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4469_, 0, v___x_4468_);
    return v___x_4469_;
}
pub unsafe fn l_Array_groupByKey___redArg(
    mut v_inst_4470_: *mut leanh::LeanObject,
    mut v_inst_4471_: *mut leanh::LeanObject,
    mut v_key_4472_: *mut leanh::LeanObject,
    mut v_xs_4473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_groups_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4477_: usize = 0;
    let mut v___x_4478_: usize = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4474_ = leanh::lean_alloc_closure(
        l_Array_groupByKey___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_4474_, 0, v_key_4472_);
    leanh::lean_closure_set(v___f_4474_, 1, v_inst_4470_);
    leanh::lean_closure_set(v___f_4474_, 2, v_inst_4471_);
    v___x_4475_ = l_Std_HashMap_keys___redArg___closed__9;
    v_groups_4476_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v_sz_4477_ = lean_array_size(v_xs_4473_);
    v___x_4478_ = 0usize;
    v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4475_,
        v_xs_4473_,
        v___f_4474_,
        v_sz_4477_,
        v___x_4478_,
        v_groups_4476_,
    );
    return v___x_4479_;
}
pub unsafe fn l_Array_groupByKey(
    mut v_00_u03b1_4480_: *mut leanh::LeanObject,
    mut v_00_u03b2_4481_: *mut leanh::LeanObject,
    mut v_inst_4482_: *mut leanh::LeanObject,
    mut v_inst_4483_: *mut leanh::LeanObject,
    mut v_key_4484_: *mut leanh::LeanObject,
    mut v_xs_4485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l_Array_groupByKey___redArg(v_inst_4482_, v_inst_4483_, v_key_4484_, v_xs_4485_);
    return v___x_4486_;
}
pub unsafe fn l_List_groupByKey___redArg___lam__0(
    mut v_x_4487_: *mut leanh::LeanObject,
    mut v_v_4488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_4488_) == 0 {
                    v___x_4493_ = leanh::lean_box(0);
                    v___y_4490_ = v___x_4493_;
                    state = 1;
                    continue;
                } else {
                    v_val_4494_ = leanh::lean_ctor_get(v_v_4488_, 0);
                    leanh::lean_inc(v_val_4494_);
                    leanh::lean_dec_ref_known(v_v_4488_, 1);
                    v___y_4490_ = v_val_4494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4491_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4491_, 0, v_x_4487_);
                leanh::lean_ctor_set(v___x_4491_, 1, v___y_4490_);
                v___x_4492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4492_, 0, v___x_4491_);
                return v___x_4492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_groupByKey___redArg___lam__1(
    mut v_key_4495_: *mut leanh::LeanObject,
    mut v_inst_4496_: *mut leanh::LeanObject,
    mut v_inst_4497_: *mut leanh::LeanObject,
    mut v_x_4498_: *mut leanh::LeanObject,
    mut v_acc_4499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_x_4498_);
    v___f_4500_ = leanh::lean_alloc_closure(
        l_List_groupByKey___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4500_, 0, v_x_4498_);
    v___x_4501_ = leanh::lean_apply_1(v_key_4495_, v_x_4498_);
    v___x_4502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_inst_4496_,
        v_inst_4497_,
        v_acc_4499_,
        v___x_4501_,
        v___f_4500_,
    );
    return v___x_4502_;
}
pub unsafe fn l_List_groupByKey___redArg(
    mut v_inst_4503_: *mut leanh::LeanObject,
    mut v_inst_4504_: *mut leanh::LeanObject,
    mut v_key_4505_: *mut leanh::LeanObject,
    mut v_xs_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4507_ = leanh::lean_alloc_closure(
        l_List_groupByKey___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_4507_, 0, v_key_4505_);
    leanh::lean_closure_set(v___f_4507_, 1, v_inst_4503_);
    leanh::lean_closure_set(v___f_4507_, 2, v_inst_4504_);
    v___x_4508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashMap_instEmptyCollection___closed__1_once),
        _init_l_Std_HashMap_instEmptyCollection___closed__1,
    );
    v___x_4509_ = l_List_foldrTR___redArg(v___f_4507_, v___x_4508_, v_xs_4506_);
    return v___x_4509_;
}
pub unsafe fn l_List_groupByKey(
    mut v_00_u03b1_4510_: *mut leanh::LeanObject,
    mut v_00_u03b2_4511_: *mut leanh::LeanObject,
    mut v_inst_4512_: *mut leanh::LeanObject,
    mut v_inst_4513_: *mut leanh::LeanObject,
    mut v_key_4514_: *mut leanh::LeanObject,
    mut v_xs_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_List_groupByKey___redArg(v_inst_4512_, v_inst_4513_, v_key_4514_, v_xs_4515_);
    return v___x_4516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Basic(builtin);
}