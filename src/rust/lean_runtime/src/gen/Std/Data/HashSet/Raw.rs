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
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint8_once, lean_unbox, lean_unbox_uint64, lean_unsigned_to_nat,
};
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instEmptyCollection___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_HashSet_Raw_term___x7em___00__closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value) as *mut LeanObject;
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value)
                as *mut LeanObject,
            4197276704451117917 as *mut LeanObject,
        ],
    };
static l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value)
                as *mut LeanObject,
            18086102783661291962 as *mut LeanObject,
        ],
    };
pub static l_Std_HashSet_Raw_term___x7em___00__closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__3_value)
                as *mut LeanObject,
            17417104850251625812 as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__5_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__7_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__9_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_HashSet_Raw_term___x7em___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__9_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__10_value)
                as *mut LeanObject,
            (((51 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_term___x7em___00__closed__13_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__4_value)
                as *mut LeanObject,
            (((50 as usize) << 1) | 1) as *mut LeanObject,
            (((50 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_term___x7em___00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value) as *mut LeanObject;
pub static mut l_Std_HashSet_Raw_term___x7em__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__13_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut LeanObject;
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut LeanObject,6049842283740396800 as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value) as *mut LeanObject;
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__1_value) as *mut LeanObject,4197276704451117917 as *mut LeanObject] };
static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw_term___x7em___00__closed__2_value) as *mut LeanObject,18086102783661291962 as *mut LeanObject] };
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value) as *mut LeanObject,8576336600160769941 as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value) as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value) as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value) as *mut LeanObject;
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1: u8 = 0;
pub static l_Std_HashSet_Raw_toList___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__10_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_Raw_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toList___redArg___closed__11_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_Raw_toList___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toList___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__11_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_ofList___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofList___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_HashSet_Raw_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_toArray___redArg___closed__1_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_HashSet_Raw_toArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_toArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_toArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_union___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_union___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_union___redArg___closed__0_value) as *mut LeanObject;
static mut l_Std_HashSet_Raw_beq___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_HashSet_Raw_beq___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_HashSet_Raw_all___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_HashSet_Raw_all___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_all___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_toList___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_ofArray___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_ofArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_ofArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 72, 97, 115, 104, 83, 101, 116, 46, 82, 97, 119, 46, 111, 102, 76,
            105, 115, 116, 32, 0,
        ],
    };
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg(
    mut v_capacity_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_unsigned_to_nat(0);
    v___x_1389_ = lean_unsigned_to_nat(4);
    v___x_1390_ = lean_nat_mul(v_capacity_1387_, v___x_1389_);
    v___x_1391_ = lean_unsigned_to_nat(3);
    v___x_1392_ = lean_nat_div(v___x_1390_, v___x_1391_);
    lean_dec(v___x_1390_);
    v___x_1393_ = l_Nat_nextPowerOfTwo(v___x_1392_);
    lean_dec(v___x_1392_);
    v___x_1394_ = lean_box(0);
    v___x_1395_ = lean_mk_array(v___x_1393_, v___x_1394_);
    v___x_1396_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1396_, 0, v___x_1388_);
    lean_ctor_set(v___x_1396_, 1, v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(
    mut v_capacity_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1398_: *mut LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_HashSet_Raw_emptyWithCapacity___redArg(v_capacity_1397_);
    lean_dec(v_capacity_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity(
    mut v_00_u03b1_1399_: *mut LeanObject,
    mut v_capacity_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = lean_unsigned_to_nat(0);
    v___x_1402_ = lean_unsigned_to_nat(4);
    v___x_1403_ = lean_nat_mul(v_capacity_1400_, v___x_1402_);
    v___x_1404_ = lean_unsigned_to_nat(3);
    v___x_1405_ = lean_nat_div(v___x_1403_, v___x_1404_);
    lean_dec(v___x_1403_);
    v___x_1406_ = l_Nat_nextPowerOfTwo(v___x_1405_);
    lean_dec(v___x_1405_);
    v___x_1407_ = lean_box(0);
    v___x_1408_ = lean_mk_array(v___x_1406_, v___x_1407_);
    v___x_1409_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1409_, 0, v___x_1401_);
    lean_ctor_set(v___x_1409_, 1, v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Std_HashSet_Raw_emptyWithCapacity___boxed(
    mut v_00_u03b1_1410_: *mut LeanObject,
    mut v_capacity_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_HashSet_Raw_emptyWithCapacity(v_00_u03b1_1410_, v_capacity_1411_);
    lean_dec(v_capacity_1411_);
    return v_res_1412_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0() -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ = lean_box(0);
    v___x_1414_ = lean_unsigned_to_nat(16);
    v___x_1415_ = lean_mk_array(v___x_1414_, v___x_1413_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1() -> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1417_ = lean_unsigned_to_nat(0);
    v___x_1418_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    return v___x_1418_;
}
pub unsafe fn l_Std_HashSet_Raw_instEmptyCollection(
    mut v_00_u03b1_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1420_;
}
pub unsafe fn l_Std_HashSet_Raw_instInhabited(
    mut v_00_u03b1_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v___x_1422_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    return v___x_1422_;
}
pub unsafe fn _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6()
-> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5;
    v___x_1464_ = l_String_toRawSubstring_x27(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(
    mut v_x_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    v___x_1489_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
    lean_inc(v_x_1486_);
    v___x_1490_ = l_Lean_Syntax_isOfKind(v_x_1486_, v___x_1489_);
    if v___x_1490_ == 0 {
        let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1486_);
        v___x_1491_ = lean_box(1);
        v___x_1492_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1492_, 0, v___x_1491_);
        lean_ctor_set(v___x_1492_, 1, v_a_1488_);
        return v___x_1492_;
    } else {
        let mut v_quotContext_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1494_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: u8 = 0;
        let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1493_ = lean_ctor_get(v_a_1487_, 1);
        v_currMacroScope_1494_ = lean_ctor_get(v_a_1487_, 2);
        v_ref_1495_ = lean_ctor_get(v_a_1487_, 5);
        v___x_1496_ = lean_unsigned_to_nat(0);
        v___x_1497_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1496_);
        v___x_1498_ = lean_unsigned_to_nat(2);
        v___x_1499_ = l_Lean_Syntax_getArg(v_x_1486_, v___x_1498_);
        lean_dec(v_x_1486_);
        v___x_1500_ = 0;
        v___x_1501_ = l_Lean_SourceInfo_fromRef(v_ref_1495_, v___x_1500_);
        v___x_1502_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
        v___x_1503_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once), _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
        v___x_1504_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7;
        lean_inc(v_currMacroScope_1494_);
        lean_inc(v_quotContext_1493_);
        v___x_1505_ =
            l_Lean_addMacroScope(v_quotContext_1493_, v___x_1504_, v_currMacroScope_1494_);
        v___x_1506_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12;
        lean_inc_n(v___x_1501_, 2);
        v___x_1507_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1507_, 0, v___x_1501_);
        lean_ctor_set(v___x_1507_, 1, v___x_1503_);
        lean_ctor_set(v___x_1507_, 2, v___x_1505_);
        lean_ctor_set(v___x_1507_, 3, v___x_1506_);
        v___x_1508_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14;
        v___x_1509_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1508_, v___x_1497_, v___x_1499_);
        v___x_1510_ = l_Lean_Syntax_node2(v___x_1501_, v___x_1502_, v___x_1507_, v___x_1509_);
        v___x_1511_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1511_, 0, v___x_1510_);
        lean_ctor_set(v___x_1511_, 1, v_a_1488_);
        return v___x_1511_;
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(
    mut v_x_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1515_: *mut LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_1512_, v_a_1513_, v_a_1514_);
    lean_dec_ref(v_a_1513_);
    return v_res_1515_;
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
    mut v_x_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: u8 = 0;
    v___x_1522_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4;
    lean_inc(v_x_1519_);
    v___x_1523_ = l_Lean_Syntax_isOfKind(v_x_1519_, v___x_1522_);
    if v___x_1523_ == 0 {
        let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1519_);
        v___x_1524_ = lean_box(0);
        v___x_1525_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1525_, 0, v___x_1524_);
        lean_ctor_set(v___x_1525_, 1, v_a_1521_);
        return v___x_1525_;
    } else {
        let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: u8 = 0;
        v___x_1526_ = lean_unsigned_to_nat(0);
        v___x_1527_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1526_);
        v___x_1528_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1;
        lean_inc(v___x_1527_);
        v___x_1529_ = l_Lean_Syntax_isOfKind(v___x_1527_, v___x_1528_);
        if v___x_1529_ == 0 {
            let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1527_);
            lean_dec(v_x_1519_);
            v___x_1530_ = lean_box(0);
            v___x_1531_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1531_, 0, v___x_1530_);
            lean_ctor_set(v___x_1531_, 1, v_a_1521_);
            return v___x_1531_;
        } else {
            let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1535_: u8 = 0;
            v___x_1532_ = lean_unsigned_to_nat(1);
            v___x_1533_ = l_Lean_Syntax_getArg(v_x_1519_, v___x_1532_);
            lean_dec(v_x_1519_);
            v___x_1534_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1533_);
            v___x_1535_ = l_Lean_Syntax_matchesNull(v___x_1533_, v___x_1534_);
            if v___x_1535_ == 0 {
                let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1533_);
                lean_dec(v___x_1527_);
                v___x_1536_ = lean_box(0);
                v___x_1537_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                lean_ctor_set(v___x_1537_, 1, v_a_1521_);
                return v___x_1537_;
            } else {
                let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1540_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1541_: u8 = 0;
                let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
                v___x_1538_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1526_);
                v___x_1539_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_1532_);
                lean_dec(v___x_1533_);
                v_ref_1540_ = l_Lean_replaceRef(v___x_1527_, v_a_1520_);
                lean_dec(v___x_1527_);
                v___x_1541_ = 0;
                v___x_1542_ = l_Lean_SourceInfo_fromRef(v_ref_1540_, v___x_1541_);
                lean_dec(v_ref_1540_);
                v___x_1543_ = l_Std_HashSet_Raw_term___x7em___00__closed__4;
                v___x_1544_ = l_Std_HashSet_Raw_term___x7em___00__closed__7;
                lean_inc(v___x_1542_);
                v___x_1545_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1545_, 0, v___x_1542_);
                lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                v___x_1546_ = l_Lean_Syntax_node3(
                    v___x_1542_,
                    v___x_1543_,
                    v___x_1538_,
                    v___x_1545_,
                    v___x_1539_,
                );
                v___x_1547_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1547_, 0, v___x_1546_);
                lean_ctor_set(v___x_1547_, 1, v_a_1521_);
                return v___x_1547_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(
    mut v_x_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1551_: *mut LeanObject = core::ptr::null_mut();
    v_res_1551_ =
        l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(
            v_x_1548_, v_a_1549_, v_a_1550_,
        );
    lean_dec(v_a_1549_);
    return v_res_1551_;
}
pub unsafe fn l_Std_HashSet_Raw_insert___redArg(
    mut v_inst_1552_: *mut LeanObject,
    mut v_inst_1553_: *mut LeanObject,
    mut v_m_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    v_buckets_1556_ = lean_ctor_get(v_m_1554_, 1);
    v___x_1557_ = lean_unsigned_to_nat(0);
    v___x_1558_ = lean_array_get_size(v_buckets_1556_);
    v___x_1559_ = lean_nat_dec_lt(v___x_1557_, v___x_1558_);
    if v___x_1559_ == 0 {
        lean_dec(v_a_1555_);
        lean_dec_ref(v_inst_1553_);
        lean_dec_ref(v_inst_1552_);
        return v_m_1554_;
    } else {
        let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
        v___x_1560_ = lean_box(0);
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
    mut v_00_u03b1_1562_: *mut LeanObject,
    mut v_inst_1563_: *mut LeanObject,
    mut v_inst_1564_: *mut LeanObject,
    mut v_m_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    v_buckets_1567_ = lean_ctor_get(v_m_1565_, 1);
    v___x_1568_ = lean_unsigned_to_nat(0);
    v___x_1569_ = lean_array_get_size(v_buckets_1567_);
    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
    if v___x_1570_ == 0 {
        lean_dec(v_a_1566_);
        lean_dec_ref(v_inst_1564_);
        lean_dec_ref(v_inst_1563_);
        return v_m_1565_;
    } else {
        let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
        v___x_1571_ = lean_box(0);
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
-> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__0_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0,
    );
    v___x_1574_ = lean_array_get_size(v___x_1573_);
    return v___x_1574_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1()
-> u8 {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    v___x_1575_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0,
    );
    v___x_1576_ = lean_unsigned_to_nat(0);
    v___x_1577_ = lean_nat_dec_lt(v___x_1576_, v___x_1575_);
    return v___x_1577_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1578_: *mut LeanObject,
    mut v_inst_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    v___x_1581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_1582_ = lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_1582_ == 0 {
        lean_dec(v_a_1580_);
        lean_dec_ref(v_inst_1579_);
        lean_dec_ref(v_inst_1578_);
        return v___x_1581_;
    } else {
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        v___x_1583_ = lean_box(0);
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
    mut v_inst_1585_: *mut LeanObject,
    mut v_inst_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1587_: *mut LeanObject = core::ptr::null_mut();
    v___f_1587_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1587_, 0, v_inst_1585_);
    lean_closure_set(v___f_1587_, 1, v_inst_1586_);
    return v___f_1587_;
}
pub unsafe fn l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(
    mut v_00_u03b1_1588_: *mut LeanObject,
    mut v_inst_1589_: *mut LeanObject,
    mut v_inst_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1591_: *mut LeanObject = core::ptr::null_mut();
    v___f_1591_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1591_, 0, v_inst_1589_);
    lean_closure_set(v___f_1591_, 1, v_inst_1590_);
    return v___f_1591_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(
    mut v_inst_1592_: *mut LeanObject,
    mut v_inst_1593_: *mut LeanObject,
    mut v_a_1594_: *mut LeanObject,
    mut v_s_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v_buckets_1596_ = lean_ctor_get(v_s_1595_, 1);
    v___x_1597_ = lean_unsigned_to_nat(0);
    v___x_1598_ = lean_array_get_size(v_buckets_1596_);
    v___x_1599_ = lean_nat_dec_lt(v___x_1597_, v___x_1598_);
    if v___x_1599_ == 0 {
        lean_dec(v_a_1594_);
        lean_dec_ref(v_inst_1593_);
        lean_dec_ref(v_inst_1592_);
        return v_s_1595_;
    } else {
        let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
        v___x_1600_ = lean_box(0);
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
    mut v_inst_1602_: *mut LeanObject,
    mut v_inst_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1604_: *mut LeanObject = core::ptr::null_mut();
    v___f_1604_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1604_, 0, v_inst_1602_);
    lean_closure_set(v___f_1604_, 1, v_inst_1603_);
    return v___f_1604_;
}
pub unsafe fn l_Std_HashSet_Raw_instInsertOfBEqOfHashable(
    mut v_00_u03b1_1605_: *mut LeanObject,
    mut v_inst_1606_: *mut LeanObject,
    mut v_inst_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1608_: *mut LeanObject = core::ptr::null_mut();
    v___f_1608_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1608_, 0, v_inst_1606_);
    lean_closure_set(v___f_1608_, 1, v_inst_1607_);
    return v___f_1608_;
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert___redArg(
    mut v_inst_1609_: *mut LeanObject,
    mut v_inst_1610_: *mut LeanObject,
    mut v_m_1611_: *mut LeanObject,
    mut v_a_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v_val_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_unused_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1613_ = lean_ctor_get(v_m_1611_, 0);
                v_buckets_1614_ = lean_ctor_get(v_m_1611_, 1);
                v___x_1615_ = lean_unsigned_to_nat(0);
                v___x_1616_ = lean_array_get_size(v_buckets_1614_);
                v___x_1617_ = lean_nat_dec_lt(v___x_1615_, v___x_1616_);
                if v___x_1617_ == 0 {
                    lean_dec(v_a_1612_);
                    lean_dec_ref(v_inst_1610_);
                    lean_dec_ref(v_inst_1609_);
                    v___x_1618_ = lean_box((v___x_1617_) as usize);
                    v___x_1619_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                    lean_ctor_set(v___x_1619_, 1, v_m_1611_);
                    return v___x_1619_;
                } else {
                    lean_inc_ref(v_inst_1610_);
                    lean_inc_n(v_a_1612_, 2);
                    v___x_1620_ = lean_apply_1(v_inst_1610_, v_a_1612_);
                    v___x_1621_ = 32u64;
                    v___x_1622_ = lean_unbox_uint64(v___x_1620_);
                    v___x_1623_ = lean_uint64_shift_right(v___x_1622_, v___x_1621_);
                    v___x_1624_ = lean_unbox_uint64(v___x_1620_);
                    lean_dec_ref(v___x_1620_);
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
                    lean_inc(v_bkt_1634_);
                    v___x_1635_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1609_,
                        v_a_1612_,
                        v_bkt_1634_,
                    );
                    if v___x_1635_ == 0 {
                        lean_inc_ref(v_buckets_1614_);
                        lean_inc(v_size_1613_);
                        v_isSharedCheck_1661_ = (!lean_is_exclusive(v_m_1611_)) as u8;
                        if v_isSharedCheck_1661_ == 0 {
                            v_unused_1662_ = lean_ctor_get(v_m_1611_, 1);
                            lean_dec(v_unused_1662_);
                            v_unused_1663_ = lean_ctor_get(v_m_1611_, 0);
                            lean_dec(v_unused_1663_);
                            v___x_1637_ = v_m_1611_;
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_m_1611_);
                            v___x_1637_ = lean_box(0);
                            v_isShared_1638_ = v_isSharedCheck_1661_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1612_);
                        lean_dec_ref(v_inst_1610_);
                        v___x_1664_ = lean_box((v___x_1635_) as usize);
                        v___x_1665_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1665_, 0, v___x_1664_);
                        lean_ctor_set(v___x_1665_, 1, v_m_1611_);
                        return v___x_1665_;
                    }
                }
            }
            1 => {
                v___x_1639_ = lean_box(0);
                v___x_1640_ = lean_unsigned_to_nat(1);
                v_size_x27_1641_ = lean_nat_add(v_size_1613_, v___x_1640_);
                lean_dec(v_size_1613_);
                lean_inc(v_bkt_1634_);
                v___x_1642_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1642_, 0, v_a_1612_);
                lean_ctor_set(v___x_1642_, 1, v___x_1639_);
                lean_ctor_set(v___x_1642_, 2, v_bkt_1634_);
                v_buckets_x27_1643_ = lean_array_uset(v_buckets_1614_, v___x_1633_, v___x_1642_);
                v___x_1644_ = lean_unsigned_to_nat(4);
                v___x_1645_ = lean_nat_mul(v_size_x27_1641_, v___x_1644_);
                v___x_1646_ = lean_unsigned_to_nat(3);
                v___x_1647_ = lean_nat_div(v___x_1645_, v___x_1646_);
                lean_dec(v___x_1645_);
                v___x_1648_ = lean_array_get_size(v_buckets_x27_1643_);
                v___x_1649_ = lean_nat_dec_le(v___x_1647_, v___x_1648_);
                lean_dec(v___x_1647_);
                if v___x_1649_ == 0 {
                    v_val_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1610_,
                        v_buckets_x27_1643_,
                    );
                    if v_isShared_1638_ == 0 {
                        lean_ctor_set(v___x_1637_, 1, v_val_1650_);
                        lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1652_ = v___x_1637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_size_x27_1641_);
                        lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_val_1650_);
                        v___x_1652_ = v_reuseFailAlloc_1655_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_1610_);
                    if v_isShared_1638_ == 0 {
                        lean_ctor_set(v___x_1637_, 1, v_buckets_x27_1643_);
                        lean_ctor_set(v___x_1637_, 0, v_size_x27_1641_);
                        v___x_1657_ = v___x_1637_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_size_x27_1641_);
                        lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_buckets_x27_1643_);
                        v___x_1657_ = v_reuseFailAlloc_1660_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1653_ = lean_box((v___x_1635_) as usize);
                v___x_1654_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1654_, 0, v___x_1653_);
                lean_ctor_set(v___x_1654_, 1, v___x_1652_);
                return v___x_1654_;
            }
            3 => {
                v___x_1658_ = lean_box((v___x_1635_) as usize);
                v___x_1659_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                lean_ctor_set(v___x_1659_, 1, v___x_1657_);
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_containsThenInsert(
    mut v_00_u03b1_1666_: *mut LeanObject,
    mut v_inst_1667_: *mut LeanObject,
    mut v_inst_1668_: *mut LeanObject,
    mut v_m_1669_: *mut LeanObject,
    mut v_a_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v_val_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_unused_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1671_ = lean_ctor_get(v_m_1669_, 0);
                v_buckets_1672_ = lean_ctor_get(v_m_1669_, 1);
                v___x_1673_ = lean_unsigned_to_nat(0);
                v___x_1674_ = lean_array_get_size(v_buckets_1672_);
                v___x_1675_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
                if v___x_1675_ == 0 {
                    lean_dec(v_a_1670_);
                    lean_dec_ref(v_inst_1668_);
                    lean_dec_ref(v_inst_1667_);
                    v___x_1676_ = lean_box((v___x_1675_) as usize);
                    v___x_1677_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1677_, 0, v___x_1676_);
                    lean_ctor_set(v___x_1677_, 1, v_m_1669_);
                    return v___x_1677_;
                } else {
                    lean_inc_ref(v_inst_1668_);
                    lean_inc_n(v_a_1670_, 2);
                    v___x_1678_ = lean_apply_1(v_inst_1668_, v_a_1670_);
                    v___x_1679_ = 32u64;
                    v___x_1680_ = lean_unbox_uint64(v___x_1678_);
                    v___x_1681_ = lean_uint64_shift_right(v___x_1680_, v___x_1679_);
                    v___x_1682_ = lean_unbox_uint64(v___x_1678_);
                    lean_dec_ref(v___x_1678_);
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
                    lean_inc(v_bkt_1692_);
                    v___x_1693_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                        v_inst_1667_,
                        v_a_1670_,
                        v_bkt_1692_,
                    );
                    if v___x_1693_ == 0 {
                        lean_inc_ref(v_buckets_1672_);
                        lean_inc(v_size_1671_);
                        v_isSharedCheck_1719_ = (!lean_is_exclusive(v_m_1669_)) as u8;
                        if v_isSharedCheck_1719_ == 0 {
                            v_unused_1720_ = lean_ctor_get(v_m_1669_, 1);
                            lean_dec(v_unused_1720_);
                            v_unused_1721_ = lean_ctor_get(v_m_1669_, 0);
                            lean_dec(v_unused_1721_);
                            v___x_1695_ = v_m_1669_;
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_m_1669_);
                            v___x_1695_ = lean_box(0);
                            v_isShared_1696_ = v_isSharedCheck_1719_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1670_);
                        lean_dec_ref(v_inst_1668_);
                        v___x_1722_ = lean_box((v___x_1693_) as usize);
                        v___x_1723_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1723_, 0, v___x_1722_);
                        lean_ctor_set(v___x_1723_, 1, v_m_1669_);
                        return v___x_1723_;
                    }
                }
            }
            1 => {
                v___x_1697_ = lean_box(0);
                v___x_1698_ = lean_unsigned_to_nat(1);
                v_size_x27_1699_ = lean_nat_add(v_size_1671_, v___x_1698_);
                lean_dec(v_size_1671_);
                lean_inc(v_bkt_1692_);
                v___x_1700_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1700_, 0, v_a_1670_);
                lean_ctor_set(v___x_1700_, 1, v___x_1697_);
                lean_ctor_set(v___x_1700_, 2, v_bkt_1692_);
                v_buckets_x27_1701_ = lean_array_uset(v_buckets_1672_, v___x_1691_, v___x_1700_);
                v___x_1702_ = lean_unsigned_to_nat(4);
                v___x_1703_ = lean_nat_mul(v_size_x27_1699_, v___x_1702_);
                v___x_1704_ = lean_unsigned_to_nat(3);
                v___x_1705_ = lean_nat_div(v___x_1703_, v___x_1704_);
                lean_dec(v___x_1703_);
                v___x_1706_ = lean_array_get_size(v_buckets_x27_1701_);
                v___x_1707_ = lean_nat_dec_le(v___x_1705_, v___x_1706_);
                lean_dec(v___x_1705_);
                if v___x_1707_ == 0 {
                    v_val_1708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_1668_,
                        v_buckets_x27_1701_,
                    );
                    if v_isShared_1696_ == 0 {
                        lean_ctor_set(v___x_1695_, 1, v_val_1708_);
                        lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1710_ = v___x_1695_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_size_x27_1699_);
                        lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_val_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1713_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_1668_);
                    if v_isShared_1696_ == 0 {
                        lean_ctor_set(v___x_1695_, 1, v_buckets_x27_1701_);
                        lean_ctor_set(v___x_1695_, 0, v_size_x27_1699_);
                        v___x_1715_ = v___x_1695_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_x27_1699_);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_buckets_x27_1701_);
                        v___x_1715_ = v_reuseFailAlloc_1718_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1711_ = lean_box((v___x_1693_) as usize);
                v___x_1712_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1712_, 0, v___x_1711_);
                lean_ctor_set(v___x_1712_, 1, v___x_1710_);
                return v___x_1712_;
            }
            3 => {
                v___x_1716_ = lean_box((v___x_1693_) as usize);
                v___x_1717_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                lean_ctor_set(v___x_1717_, 1, v___x_1715_);
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_contains___redArg(
    mut v_inst_1724_: *mut LeanObject,
    mut v_inst_1725_: *mut LeanObject,
    mut v_m_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    v_buckets_1728_ = lean_ctor_get(v_m_1726_, 1);
    v___x_1729_ = lean_unsigned_to_nat(0);
    v___x_1730_ = lean_array_get_size(v_buckets_1728_);
    v___x_1731_ = lean_nat_dec_lt(v___x_1729_, v___x_1730_);
    if v___x_1731_ == 0 {
        lean_dec(v_a_1727_);
        lean_dec_ref(v_inst_1725_);
        lean_dec_ref(v_inst_1724_);
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
    mut v_inst_1733_: *mut LeanObject,
    mut v_inst_1734_: *mut LeanObject,
    mut v_m_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1737_: u8 = 0;
    let mut v_r_1738_: *mut LeanObject = core::ptr::null_mut();
    v_res_1737_ =
        l_Std_HashSet_Raw_contains___redArg(v_inst_1733_, v_inst_1734_, v_m_1735_, v_a_1736_);
    lean_dec_ref(v_m_1735_);
    v_r_1738_ = lean_box((v_res_1737_) as usize);
    return v_r_1738_;
}
pub unsafe fn l_Std_HashSet_Raw_contains(
    mut v_00_u03b1_1739_: *mut LeanObject,
    mut v_inst_1740_: *mut LeanObject,
    mut v_inst_1741_: *mut LeanObject,
    mut v_m_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    v_buckets_1744_ = lean_ctor_get(v_m_1742_, 1);
    v___x_1745_ = lean_unsigned_to_nat(0);
    v___x_1746_ = lean_array_get_size(v_buckets_1744_);
    v___x_1747_ = lean_nat_dec_lt(v___x_1745_, v___x_1746_);
    if v___x_1747_ == 0 {
        lean_dec(v_a_1743_);
        lean_dec_ref(v_inst_1741_);
        lean_dec_ref(v_inst_1740_);
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
    mut v_00_u03b1_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_inst_1751_: *mut LeanObject,
    mut v_m_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1754_: u8 = 0;
    let mut v_r_1755_: *mut LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Std_HashSet_Raw_contains(
        v_00_u03b1_1749_,
        v_inst_1750_,
        v_inst_1751_,
        v_m_1752_,
        v_a_1753_,
    );
    lean_dec_ref(v_m_1752_);
    v_r_1755_ = lean_box((v_res_1754_) as usize);
    return v_r_1755_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
    mut v_00_u03b1_1756_: *mut LeanObject,
    mut v_inst_1757_: *mut LeanObject,
    mut v_inst_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = lean_box(0);
    return v___x_1759_;
}
pub unsafe fn l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(
    mut v_00_u03b1_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1763_: *mut LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(
        v_00_u03b1_1760_,
        v_inst_1761_,
        v_inst_1762_,
    );
    lean_dec_ref(v_inst_1762_);
    lean_dec_ref(v_inst_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem___redArg(
    mut v_inst_1764_: *mut LeanObject,
    mut v_inst_1765_: *mut LeanObject,
    mut v_m_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
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
    mut v_inst_1769_: *mut LeanObject,
    mut v_inst_1770_: *mut LeanObject,
    mut v_m_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1773_: u8 = 0;
    let mut v_r_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Std_HashSet_Raw_instDecidableMem___redArg(
        v_inst_1769_,
        v_inst_1770_,
        v_m_1771_,
        v_a_1772_,
    );
    lean_dec_ref(v_m_1771_);
    v_r_1774_ = lean_box((v_res_1773_) as usize);
    return v_r_1774_;
}
pub unsafe fn l_Std_HashSet_Raw_instDecidableMem(
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_inst_1776_: *mut LeanObject,
    mut v_inst_1777_: *mut LeanObject,
    mut v_m_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
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
    mut v_00_u03b1_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
    mut v_m_1784_: *mut LeanObject,
    mut v_a_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1786_: u8 = 0;
    let mut v_r_1787_: *mut LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_HashSet_Raw_instDecidableMem(
        v_00_u03b1_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_m_1784_,
        v_a_1785_,
    );
    lean_dec_ref(v_m_1784_);
    v_r_1787_ = lean_box((v_res_1786_) as usize);
    return v_r_1787_;
}
pub unsafe fn l_Std_HashSet_Raw_erase___redArg(
    mut v_inst_1788_: *mut LeanObject,
    mut v_inst_1789_: *mut LeanObject,
    mut v_m_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: u8 = 0;
    v_buckets_1792_ = lean_ctor_get(v_m_1790_, 1);
    v___x_1793_ = lean_unsigned_to_nat(0);
    v___x_1794_ = lean_array_get_size(v_buckets_1792_);
    v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
    if v___x_1795_ == 0 {
        lean_dec(v_a_1791_);
        lean_dec_ref(v_inst_1789_);
        lean_dec_ref(v_inst_1788_);
        return v_m_1790_;
    } else {
        let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1797_: *mut LeanObject,
    mut v_inst_1798_: *mut LeanObject,
    mut v_inst_1799_: *mut LeanObject,
    mut v_m_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    v_buckets_1802_ = lean_ctor_get(v_m_1800_, 1);
    v___x_1803_ = lean_unsigned_to_nat(0);
    v___x_1804_ = lean_array_get_size(v_buckets_1802_);
    v___x_1805_ = lean_nat_dec_lt(v___x_1803_, v___x_1804_);
    if v___x_1805_ == 0 {
        lean_dec(v_a_1801_);
        lean_dec_ref(v_inst_1799_);
        lean_dec_ref(v_inst_1798_);
        return v_m_1800_;
    } else {
        let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
        v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
            v_inst_1798_,
            v_inst_1799_,
            v_m_1800_,
            v_a_1801_,
        );
        return v___x_1806_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_size___redArg(mut v_m_1807_: *mut LeanObject) -> *mut LeanObject {
    let mut v_size_1808_: *mut LeanObject = core::ptr::null_mut();
    v_size_1808_ = lean_ctor_get(v_m_1807_, 0);
    lean_inc(v_size_1808_);
    return v_size_1808_;
}
pub unsafe fn l_Std_HashSet_Raw_size___redArg___boxed(
    mut v_m_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1810_: *mut LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Std_HashSet_Raw_size___redArg(v_m_1809_);
    lean_dec_ref(v_m_1809_);
    return v_res_1810_;
}
pub unsafe fn l_Std_HashSet_Raw_size(
    mut v_00_u03b1_1811_: *mut LeanObject,
    mut v_m_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1813_: *mut LeanObject = core::ptr::null_mut();
    v_size_1813_ = lean_ctor_get(v_m_1812_, 0);
    lean_inc(v_size_1813_);
    return v_size_1813_;
}
pub unsafe fn l_Std_HashSet_Raw_size___boxed(
    mut v_00_u03b1_1814_: *mut LeanObject,
    mut v_m_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1816_: *mut LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_HashSet_Raw_size(v_00_u03b1_1814_, v_m_1815_);
    lean_dec_ref(v_m_1815_);
    return v_res_1816_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f___redArg(
    mut v_inst_1817_: *mut LeanObject,
    mut v_inst_1818_: *mut LeanObject,
    mut v_m_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    v_buckets_1821_ = lean_ctor_get(v_m_1819_, 1);
    v___x_1822_ = lean_unsigned_to_nat(0);
    v___x_1823_ = lean_array_get_size(v_buckets_1821_);
    v___x_1824_ = lean_nat_dec_lt(v___x_1822_, v___x_1823_);
    if v___x_1824_ == 0 {
        let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1820_);
        lean_dec_ref(v_inst_1818_);
        lean_dec_ref(v_inst_1817_);
        v___x_1825_ = lean_box(0);
        return v___x_1825_;
    } else {
        let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1827_: *mut LeanObject,
    mut v_inst_1828_: *mut LeanObject,
    mut v_m_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1831_: *mut LeanObject = core::ptr::null_mut();
    v_res_1831_ =
        l_Std_HashSet_Raw_get_x3f___redArg(v_inst_1827_, v_inst_1828_, v_m_1829_, v_a_1830_);
    lean_dec_ref(v_m_1829_);
    return v_res_1831_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x3f(
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_inst_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
    mut v_m_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    v_buckets_1837_ = lean_ctor_get(v_m_1835_, 1);
    v___x_1838_ = lean_unsigned_to_nat(0);
    v___x_1839_ = lean_array_get_size(v_buckets_1837_);
    v___x_1840_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
    if v___x_1840_ == 0 {
        let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1836_);
        lean_dec_ref(v_inst_1834_);
        lean_dec_ref(v_inst_1833_);
        v___x_1841_ = lean_box(0);
        return v___x_1841_;
    } else {
        let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1843_: *mut LeanObject,
    mut v_inst_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_m_1846_: *mut LeanObject,
    mut v_a_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_HashSet_Raw_get_x3f(
        v_00_u03b1_1843_,
        v_inst_1844_,
        v_inst_1845_,
        v_m_1846_,
        v_a_1847_,
    );
    lean_dec_ref(v_m_1846_);
    return v_res_1848_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg(
    mut v_inst_1849_: *mut LeanObject,
    mut v_inst_1850_: *mut LeanObject,
    mut v_m_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1849_,
        v_inst_1850_,
        v_m_1851_,
        v_a_1852_,
    );
    return v___x_1853_;
}
pub unsafe fn l_Std_HashSet_Raw_get___redArg___boxed(
    mut v_inst_1854_: *mut LeanObject,
    mut v_inst_1855_: *mut LeanObject,
    mut v_m_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Std_HashSet_Raw_get___redArg(v_inst_1854_, v_inst_1855_, v_m_1856_, v_a_1857_);
    lean_dec_ref(v_m_1856_);
    return v_res_1858_;
}
pub unsafe fn l_Std_HashSet_Raw_get(
    mut v_00_u03b1_1859_: *mut LeanObject,
    mut v_inst_1860_: *mut LeanObject,
    mut v_inst_1861_: *mut LeanObject,
    mut v_m_1862_: *mut LeanObject,
    mut v_a_1863_: *mut LeanObject,
    mut v_h_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_1860_,
        v_inst_1861_,
        v_m_1862_,
        v_a_1863_,
    );
    return v___x_1865_;
}
pub unsafe fn l_Std_HashSet_Raw_get___boxed(
    mut v_00_u03b1_1866_: *mut LeanObject,
    mut v_inst_1867_: *mut LeanObject,
    mut v_inst_1868_: *mut LeanObject,
    mut v_m_1869_: *mut LeanObject,
    mut v_a_1870_: *mut LeanObject,
    mut v_h_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1872_: *mut LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Std_HashSet_Raw_get(
        v_00_u03b1_1866_,
        v_inst_1867_,
        v_inst_1868_,
        v_m_1869_,
        v_a_1870_,
        v_h_1871_,
    );
    lean_dec_ref(v_m_1869_);
    return v_res_1872_;
}
pub unsafe fn l_Std_HashSet_Raw_getD___redArg(
    mut v_inst_1873_: *mut LeanObject,
    mut v_inst_1874_: *mut LeanObject,
    mut v_m_1875_: *mut LeanObject,
    mut v_a_1876_: *mut LeanObject,
    mut v_fallback_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    v_buckets_1878_ = lean_ctor_get(v_m_1875_, 1);
    v___x_1879_ = lean_unsigned_to_nat(0);
    v___x_1880_ = lean_array_get_size(v_buckets_1878_);
    v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
    if v___x_1881_ == 0 {
        lean_dec(v_a_1876_);
        lean_dec_ref(v_inst_1874_);
        lean_dec_ref(v_inst_1873_);
        lean_inc(v_fallback_1877_);
        return v_fallback_1877_;
    } else {
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1883_: *mut LeanObject,
    mut v_inst_1884_: *mut LeanObject,
    mut v_m_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_fallback_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1888_: *mut LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Std_HashSet_Raw_getD___redArg(
        v_inst_1883_,
        v_inst_1884_,
        v_m_1885_,
        v_a_1886_,
        v_fallback_1887_,
    );
    lean_dec(v_fallback_1887_);
    lean_dec_ref(v_m_1885_);
    return v_res_1888_;
}
pub unsafe fn l_Std_HashSet_Raw_getD(
    mut v_00_u03b1_1889_: *mut LeanObject,
    mut v_inst_1890_: *mut LeanObject,
    mut v_inst_1891_: *mut LeanObject,
    mut v_m_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_fallback_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    v_buckets_1895_ = lean_ctor_get(v_m_1892_, 1);
    v___x_1896_ = lean_unsigned_to_nat(0);
    v___x_1897_ = lean_array_get_size(v_buckets_1895_);
    v___x_1898_ = lean_nat_dec_lt(v___x_1896_, v___x_1897_);
    if v___x_1898_ == 0 {
        lean_dec(v_a_1893_);
        lean_dec_ref(v_inst_1891_);
        lean_dec_ref(v_inst_1890_);
        lean_inc(v_fallback_1894_);
        return v_fallback_1894_;
    } else {
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1900_: *mut LeanObject,
    mut v_inst_1901_: *mut LeanObject,
    mut v_inst_1902_: *mut LeanObject,
    mut v_m_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_fallback_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1906_: *mut LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Std_HashSet_Raw_getD(
        v_00_u03b1_1900_,
        v_inst_1901_,
        v_inst_1902_,
        v_m_1903_,
        v_a_1904_,
        v_fallback_1905_,
    );
    lean_dec(v_fallback_1905_);
    lean_dec_ref(v_m_1903_);
    return v_res_1906_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21___redArg(
    mut v_inst_1907_: *mut LeanObject,
    mut v_inst_1908_: *mut LeanObject,
    mut v_inst_1909_: *mut LeanObject,
    mut v_m_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    v_buckets_1912_ = lean_ctor_get(v_m_1910_, 1);
    v___x_1913_ = lean_unsigned_to_nat(0);
    v___x_1914_ = lean_array_get_size(v_buckets_1912_);
    v___x_1915_ = lean_nat_dec_lt(v___x_1913_, v___x_1914_);
    if v___x_1915_ == 0 {
        lean_dec(v_a_1911_);
        lean_dec_ref(v_inst_1908_);
        lean_dec_ref(v_inst_1907_);
        lean_inc(v_inst_1909_);
        return v_inst_1909_;
    } else {
        let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1917_: *mut LeanObject,
    mut v_inst_1918_: *mut LeanObject,
    mut v_inst_1919_: *mut LeanObject,
    mut v_m_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1922_: *mut LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_HashSet_Raw_get_x21___redArg(
        v_inst_1917_,
        v_inst_1918_,
        v_inst_1919_,
        v_m_1920_,
        v_a_1921_,
    );
    lean_dec_ref(v_m_1920_);
    lean_dec(v_inst_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_HashSet_Raw_get_x21(
    mut v_00_u03b1_1923_: *mut LeanObject,
    mut v_inst_1924_: *mut LeanObject,
    mut v_inst_1925_: *mut LeanObject,
    mut v_inst_1926_: *mut LeanObject,
    mut v_m_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    v_buckets_1929_ = lean_ctor_get(v_m_1927_, 1);
    v___x_1930_ = lean_unsigned_to_nat(0);
    v___x_1931_ = lean_array_get_size(v_buckets_1929_);
    v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
    if v___x_1932_ == 0 {
        lean_dec(v_a_1928_);
        lean_dec_ref(v_inst_1925_);
        lean_dec_ref(v_inst_1924_);
        lean_inc(v_inst_1926_);
        return v_inst_1926_;
    } else {
        let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1934_: *mut LeanObject,
    mut v_inst_1935_: *mut LeanObject,
    mut v_inst_1936_: *mut LeanObject,
    mut v_inst_1937_: *mut LeanObject,
    mut v_m_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1940_: *mut LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Std_HashSet_Raw_get_x21(
        v_00_u03b1_1934_,
        v_inst_1935_,
        v_inst_1936_,
        v_inst_1937_,
        v_m_1938_,
        v_a_1939_,
    );
    lean_dec_ref(v_m_1938_);
    lean_dec(v_inst_1937_);
    return v_res_1940_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg(mut v_m_1941_: *mut LeanObject) -> u8 {
    let mut v_size_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    v_size_1942_ = lean_ctor_get(v_m_1941_, 0);
    v___x_1943_ = lean_unsigned_to_nat(0);
    v___x_1944_ = lean_nat_dec_eq(v_size_1942_, v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___redArg___boxed(
    mut v_m_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1946_: u8 = 0;
    let mut v_r_1947_: *mut LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_1945_);
    lean_dec_ref(v_m_1945_);
    v_r_1947_ = lean_box((v_res_1946_) as usize);
    return v_r_1947_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty(
    mut v_00_u03b1_1948_: *mut LeanObject,
    mut v_m_1949_: *mut LeanObject,
) -> u8 {
    let mut v_size_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    v_size_1950_ = lean_ctor_get(v_m_1949_, 0);
    v___x_1951_ = lean_unsigned_to_nat(0);
    v___x_1952_ = lean_nat_dec_eq(v_size_1950_, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Std_HashSet_Raw_isEmpty___boxed(
    mut v_00_u03b1_1953_: *mut LeanObject,
    mut v_m_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1955_: u8 = 0;
    let mut v_r_1956_: *mut LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_1953_, v_m_1954_);
    lean_dec_ref(v_m_1954_);
    v_r_1956_ = lean_box((v_res_1955_) as usize);
    return v_r_1956_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__0(
    mut v_a_1957_: *mut LeanObject,
    mut v_b_1958_: *mut LeanObject,
    mut v_d_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1960_, 0, v_a_1957_);
    lean_ctor_set(v___x_1960_, 1, v_d_1959_);
    return v___x_1960_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg___lam__1(
    mut v___x_1961_: *mut LeanObject,
    mut v___f_1962_: *mut LeanObject,
    mut v_l_1963_: *mut LeanObject,
    mut v_acc_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1961_,
        v___f_1962_,
        v_acc_1964_,
        v_l_1963_,
    );
    return v___x_1965_;
}
pub unsafe fn l_Std_HashSet_Raw_toList___redArg(mut v_m_1989_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    v___x_1990_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_1991_ = lean_ctor_get(v_m_1989_, 1);
    lean_inc_ref(v_buckets_1991_);
    lean_dec_ref(v_m_1989_);
    v___x_1992_ = lean_box(0);
    v___x_1993_ = lean_array_get_size(v_buckets_1991_);
    v___x_1994_ = lean_unsigned_to_nat(0);
    v___x_1995_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
    if v___x_1995_ == 0 {
        lean_dec_ref(v_buckets_1991_);
        return v___x_1992_;
    } else {
        let mut v___f_1996_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: usize = 0;
        let mut v___x_1998_: usize = 0;
        let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
        v___f_1996_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_1997_ = lean_usize_of_nat(v___x_1993_);
        v___x_1998_ = 0usize;
        v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_2000_: *mut LeanObject,
    mut v_m_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    v___x_2002_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2003_ = lean_ctor_get(v_m_2001_, 1);
    lean_inc_ref(v_buckets_2003_);
    lean_dec_ref(v_m_2001_);
    v___x_2004_ = lean_box(0);
    v___x_2005_ = lean_array_get_size(v_buckets_2003_);
    v___x_2006_ = lean_unsigned_to_nat(0);
    v___x_2007_ = lean_nat_dec_lt(v___x_2006_, v___x_2005_);
    if v___x_2007_ == 0 {
        lean_dec_ref(v_buckets_2003_);
        return v___x_2004_;
    } else {
        let mut v___f_2008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: usize = 0;
        let mut v___x_2010_: usize = 0;
        let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
        v___f_2008_ = l_Std_HashSet_Raw_toList___redArg___closed__11;
        v___x_2009_ = lean_usize_of_nat(v___x_2005_);
        v___x_2010_ = 0usize;
        v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_inst_2016_: *mut LeanObject,
    mut v_inst_2017_: *mut LeanObject,
    mut v_l_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    v___x_2019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2020_ = lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2020_ == 0 {
        lean_dec(v_l_2018_);
        lean_dec_ref(v_inst_2017_);
        lean_dec_ref(v_inst_2016_);
        return v___x_2019_;
    } else {
        let mut v___f_2021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2023_: *mut LeanObject,
    mut v_inst_2024_: *mut LeanObject,
    mut v_inst_2025_: *mut LeanObject,
    mut v_l_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    v___x_2027_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2028_ = lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2028_ == 0 {
        lean_dec(v_l_2026_);
        lean_dec_ref(v_inst_2025_);
        lean_dec_ref(v_inst_2024_);
        return v___x_2027_;
    } else {
        let mut v___f_2029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_f_2031_: *mut LeanObject,
    mut v_b_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_x_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2035_ = lean_apply_2(v_f_2031_, v_b_2032_, v_a_2033_);
    return v___x_2035_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg___lam__1(
    mut v_inst_2036_: *mut LeanObject,
    mut v___f_2037_: *mut LeanObject,
    mut v_acc_2038_: *mut LeanObject,
    mut v_l_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    v___x_2040_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2036_,
        v___f_2037_,
        v_acc_2038_,
        v_l_2039_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Std_HashSet_Raw_foldM___redArg(
    mut v_inst_2041_: *mut LeanObject,
    mut v_f_2042_: *mut LeanObject,
    mut v_init_2043_: *mut LeanObject,
    mut v_b_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    v_buckets_2045_ = lean_ctor_get(v_b_2044_, 1);
    lean_inc_ref(v_buckets_2045_);
    lean_dec_ref(v_b_2044_);
    v___x_2046_ = lean_unsigned_to_nat(0);
    v___x_2047_ = lean_array_get_size(v_buckets_2045_);
    v___x_2048_ = lean_nat_dec_lt(v___x_2046_, v___x_2047_);
    if v___x_2048_ == 0 {
        let mut v_toApplicative_2049_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2045_);
        lean_dec(v_f_2042_);
        v_toApplicative_2049_ = lean_ctor_get(v_inst_2041_, 0);
        lean_inc_ref(v_toApplicative_2049_);
        lean_dec_ref(v_inst_2041_);
        v_toPure_2050_ = lean_ctor_get(v_toApplicative_2049_, 1);
        lean_inc(v_toPure_2050_);
        lean_dec_ref(v_toApplicative_2049_);
        v___x_2051_ = lean_apply_2(v_toPure_2050_, lean_box(0), v_init_2043_);
        return v___x_2051_;
    } else {
        let mut v___f_2052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: u8 = 0;
        v___f_2052_ = lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2052_, 0, v_f_2042_);
        lean_inc_ref(v_inst_2041_);
        v___f_2053_ = lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2053_, 0, v_inst_2041_);
        lean_closure_set(v___f_2053_, 1, v___f_2052_);
        v___x_2054_ = lean_nat_dec_le(v___x_2047_, v___x_2047_);
        if v___x_2054_ == 0 {
            if v___x_2048_ == 0 {
                let mut v_toApplicative_2055_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2056_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2053_);
                lean_dec_ref(v_buckets_2045_);
                v_toApplicative_2055_ = lean_ctor_get(v_inst_2041_, 0);
                lean_inc_ref(v_toApplicative_2055_);
                lean_dec_ref(v_inst_2041_);
                v_toPure_2056_ = lean_ctor_get(v_toApplicative_2055_, 1);
                lean_inc(v_toPure_2056_);
                lean_dec_ref(v_toApplicative_2055_);
                v___x_2057_ = lean_apply_2(v_toPure_2056_, lean_box(0), v_init_2043_);
                return v___x_2057_;
            } else {
                let mut v___x_2058_: usize = 0;
                let mut v___x_2059_: usize = 0;
                let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
                v___x_2058_ = 0usize;
                v___x_2059_ = lean_usize_of_nat(v___x_2047_);
                v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
            v___x_2061_ = 0usize;
            v___x_2062_ = lean_usize_of_nat(v___x_2047_);
            v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_2064_: *mut LeanObject,
    mut v_m_2065_: *mut LeanObject,
    mut v_inst_2066_: *mut LeanObject,
    mut v_00_u03b2_2067_: *mut LeanObject,
    mut v_f_2068_: *mut LeanObject,
    mut v_init_2069_: *mut LeanObject,
    mut v_b_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    v_buckets_2071_ = lean_ctor_get(v_b_2070_, 1);
    lean_inc_ref(v_buckets_2071_);
    lean_dec_ref(v_b_2070_);
    v___x_2072_ = lean_unsigned_to_nat(0);
    v___x_2073_ = lean_array_get_size(v_buckets_2071_);
    v___x_2074_ = lean_nat_dec_lt(v___x_2072_, v___x_2073_);
    if v___x_2074_ == 0 {
        let mut v_toApplicative_2075_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2071_);
        lean_dec(v_f_2068_);
        v_toApplicative_2075_ = lean_ctor_get(v_inst_2066_, 0);
        lean_inc_ref(v_toApplicative_2075_);
        lean_dec_ref(v_inst_2066_);
        v_toPure_2076_ = lean_ctor_get(v_toApplicative_2075_, 1);
        lean_inc(v_toPure_2076_);
        lean_dec_ref(v_toApplicative_2075_);
        v___x_2077_ = lean_apply_2(v_toPure_2076_, lean_box(0), v_init_2069_);
        return v___x_2077_;
    } else {
        let mut v___f_2078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: u8 = 0;
        v___f_2078_ = lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2078_, 0, v_f_2068_);
        lean_inc_ref(v_inst_2066_);
        v___f_2079_ = lean_alloc_closure(
            l_Std_HashSet_Raw_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2079_, 0, v_inst_2066_);
        lean_closure_set(v___f_2079_, 1, v___f_2078_);
        v___x_2080_ = lean_nat_dec_le(v___x_2073_, v___x_2073_);
        if v___x_2080_ == 0 {
            if v___x_2074_ == 0 {
                let mut v_toApplicative_2081_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2082_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2079_);
                lean_dec_ref(v_buckets_2071_);
                v_toApplicative_2081_ = lean_ctor_get(v_inst_2066_, 0);
                lean_inc_ref(v_toApplicative_2081_);
                lean_dec_ref(v_inst_2066_);
                v_toPure_2082_ = lean_ctor_get(v_toApplicative_2081_, 1);
                lean_inc(v_toPure_2082_);
                lean_dec_ref(v_toApplicative_2081_);
                v___x_2083_ = lean_apply_2(v_toPure_2082_, lean_box(0), v_init_2069_);
                return v___x_2083_;
            } else {
                let mut v___x_2084_: usize = 0;
                let mut v___x_2085_: usize = 0;
                let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
                v___x_2084_ = 0usize;
                v___x_2085_ = lean_usize_of_nat(v___x_2073_);
                v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
            v___x_2087_ = 0usize;
            v___x_2088_ = lean_usize_of_nat(v___x_2073_);
            v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_2090_: *mut LeanObject,
    mut v_x1_2091_: *mut LeanObject,
    mut v_x2_2092_: *mut LeanObject,
    mut v_x3_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v___x_2094_ = lean_apply_2(v_f_2090_, v_x1_2091_, v_x2_2092_);
    return v___x_2094_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg___lam__1(
    mut v___x_2095_: *mut LeanObject,
    mut v___f_2096_: *mut LeanObject,
    mut v_acc_2097_: *mut LeanObject,
    mut v_l_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2095_,
        v___f_2096_,
        v_acc_2097_,
        v_l_2098_,
    );
    return v___x_2099_;
}
pub unsafe fn l_Std_HashSet_Raw_fold___redArg(
    mut v_f_2100_: *mut LeanObject,
    mut v_init_2101_: *mut LeanObject,
    mut v_m_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: u8 = 0;
    v___x_2103_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2104_ = lean_ctor_get(v_m_2102_, 1);
    lean_inc_ref(v_buckets_2104_);
    lean_dec_ref(v_m_2102_);
    v___x_2105_ = lean_unsigned_to_nat(0);
    v___x_2106_ = lean_array_get_size(v_buckets_2104_);
    v___x_2107_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
    if v___x_2107_ == 0 {
        lean_dec_ref(v_buckets_2104_);
        lean_dec(v_f_2100_);
        return v_init_2101_;
    } else {
        let mut v___f_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: u8 = 0;
        v___f_2108_ = lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2108_, 0, v_f_2100_);
        v___f_2109_ = lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2109_, 0, v___x_2103_);
        lean_closure_set(v___f_2109_, 1, v___f_2108_);
        v___x_2110_ = lean_nat_dec_le(v___x_2106_, v___x_2106_);
        if v___x_2110_ == 0 {
            if v___x_2107_ == 0 {
                lean_dec_ref(v___f_2109_);
                lean_dec_ref(v_buckets_2104_);
                return v_init_2101_;
            } else {
                let mut v___x_2111_: usize = 0;
                let mut v___x_2112_: usize = 0;
                let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
                v___x_2111_ = 0usize;
                v___x_2112_ = lean_usize_of_nat(v___x_2106_);
                v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
            v___x_2114_ = 0usize;
            v___x_2115_ = lean_usize_of_nat(v___x_2106_);
            v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_2117_: *mut LeanObject,
    mut v_00_u03b2_2118_: *mut LeanObject,
    mut v_f_2119_: *mut LeanObject,
    mut v_init_2120_: *mut LeanObject,
    mut v_m_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    v___x_2122_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2123_ = lean_ctor_get(v_m_2121_, 1);
    lean_inc_ref(v_buckets_2123_);
    lean_dec_ref(v_m_2121_);
    v___x_2124_ = lean_unsigned_to_nat(0);
    v___x_2125_ = lean_array_get_size(v_buckets_2123_);
    v___x_2126_ = lean_nat_dec_lt(v___x_2124_, v___x_2125_);
    if v___x_2126_ == 0 {
        lean_dec_ref(v_buckets_2123_);
        lean_dec(v_f_2119_);
        return v_init_2120_;
    } else {
        let mut v___f_2127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: u8 = 0;
        v___f_2127_ = lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2127_, 0, v_f_2119_);
        v___f_2128_ = lean_alloc_closure(
            l_Std_HashSet_Raw_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2128_, 0, v___x_2122_);
        lean_closure_set(v___f_2128_, 1, v___f_2127_);
        v___x_2129_ = lean_nat_dec_le(v___x_2125_, v___x_2125_);
        if v___x_2129_ == 0 {
            if v___x_2126_ == 0 {
                lean_dec_ref(v___f_2128_);
                lean_dec_ref(v_buckets_2123_);
                return v_init_2120_;
            } else {
                let mut v___x_2130_: usize = 0;
                let mut v___x_2131_: usize = 0;
                let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
                v___x_2130_ = 0usize;
                v___x_2131_ = lean_usize_of_nat(v___x_2125_);
                v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
            v___x_2133_ = 0usize;
            v___x_2134_ = lean_usize_of_nat(v___x_2125_);
            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_2136_: *mut LeanObject,
    mut v_x_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = lean_apply_1(v_f_2136_, v___y_2138_);
    return v___x_2140_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg___lam__1(
    mut v_inst_2141_: *mut LeanObject,
    mut v___f_2142_: *mut LeanObject,
    mut v_x_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2145_ = lean_box(0);
    v___x_2146_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_2141_,
        v___f_2142_,
        v___x_2145_,
        v___y_2144_,
    );
    return v___x_2146_;
}
pub unsafe fn l_Std_HashSet_Raw_forM___redArg(
    mut v_inst_2147_: *mut LeanObject,
    mut v_f_2148_: *mut LeanObject,
    mut v_b_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    v_buckets_2150_ = lean_ctor_get(v_b_2149_, 1);
    lean_inc_ref(v_buckets_2150_);
    lean_dec_ref(v_b_2149_);
    v___x_2151_ = lean_unsigned_to_nat(0);
    v___x_2152_ = lean_array_get_size(v_buckets_2150_);
    v___x_2153_ = lean_box(0);
    v___x_2154_ = lean_nat_dec_lt(v___x_2151_, v___x_2152_);
    if v___x_2154_ == 0 {
        let mut v_toApplicative_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2150_);
        lean_dec(v_f_2148_);
        v_toApplicative_2155_ = lean_ctor_get(v_inst_2147_, 0);
        lean_inc_ref(v_toApplicative_2155_);
        lean_dec_ref(v_inst_2147_);
        v_toPure_2156_ = lean_ctor_get(v_toApplicative_2155_, 1);
        lean_inc(v_toPure_2156_);
        lean_dec_ref(v_toApplicative_2155_);
        v___x_2157_ = lean_apply_2(v_toPure_2156_, lean_box(0), v___x_2153_);
        return v___x_2157_;
    } else {
        let mut v___f_2158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: u8 = 0;
        v___f_2158_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2158_, 0, v_f_2148_);
        lean_inc_ref(v_inst_2147_);
        v___f_2159_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2159_, 0, v_inst_2147_);
        lean_closure_set(v___f_2159_, 1, v___f_2158_);
        v___x_2160_ = lean_nat_dec_le(v___x_2152_, v___x_2152_);
        if v___x_2160_ == 0 {
            if v___x_2154_ == 0 {
                let mut v_toApplicative_2161_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2162_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2159_);
                lean_dec_ref(v_buckets_2150_);
                v_toApplicative_2161_ = lean_ctor_get(v_inst_2147_, 0);
                lean_inc_ref(v_toApplicative_2161_);
                lean_dec_ref(v_inst_2147_);
                v_toPure_2162_ = lean_ctor_get(v_toApplicative_2161_, 1);
                lean_inc(v_toPure_2162_);
                lean_dec_ref(v_toApplicative_2161_);
                v___x_2163_ = lean_apply_2(v_toPure_2162_, lean_box(0), v___x_2153_);
                return v___x_2163_;
            } else {
                let mut v___x_2164_: usize = 0;
                let mut v___x_2165_: usize = 0;
                let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
                v___x_2164_ = 0usize;
                v___x_2165_ = lean_usize_of_nat(v___x_2152_);
                v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
            v___x_2167_ = 0usize;
            v___x_2168_ = lean_usize_of_nat(v___x_2152_);
            v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_2170_: *mut LeanObject,
    mut v_m_2171_: *mut LeanObject,
    mut v_inst_2172_: *mut LeanObject,
    mut v_f_2173_: *mut LeanObject,
    mut v_b_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    v_buckets_2175_ = lean_ctor_get(v_b_2174_, 1);
    lean_inc_ref(v_buckets_2175_);
    lean_dec_ref(v_b_2174_);
    v___x_2176_ = lean_unsigned_to_nat(0);
    v___x_2177_ = lean_array_get_size(v_buckets_2175_);
    v___x_2178_ = lean_box(0);
    v___x_2179_ = lean_nat_dec_lt(v___x_2176_, v___x_2177_);
    if v___x_2179_ == 0 {
        let mut v_toApplicative_2180_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2175_);
        lean_dec(v_f_2173_);
        v_toApplicative_2180_ = lean_ctor_get(v_inst_2172_, 0);
        lean_inc_ref(v_toApplicative_2180_);
        lean_dec_ref(v_inst_2172_);
        v_toPure_2181_ = lean_ctor_get(v_toApplicative_2180_, 1);
        lean_inc(v_toPure_2181_);
        lean_dec_ref(v_toApplicative_2180_);
        v___x_2182_ = lean_apply_2(v_toPure_2181_, lean_box(0), v___x_2178_);
        return v___x_2182_;
    } else {
        let mut v___f_2183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: u8 = 0;
        v___f_2183_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2183_, 0, v_f_2173_);
        lean_inc_ref(v_inst_2172_);
        v___f_2184_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2184_, 0, v_inst_2172_);
        lean_closure_set(v___f_2184_, 1, v___f_2183_);
        v___x_2185_ = lean_nat_dec_le(v___x_2177_, v___x_2177_);
        if v___x_2185_ == 0 {
            if v___x_2179_ == 0 {
                let mut v_toApplicative_2186_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2187_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2184_);
                lean_dec_ref(v_buckets_2175_);
                v_toApplicative_2186_ = lean_ctor_get(v_inst_2172_, 0);
                lean_inc_ref(v_toApplicative_2186_);
                lean_dec_ref(v_inst_2172_);
                v_toPure_2187_ = lean_ctor_get(v_toApplicative_2186_, 1);
                lean_inc(v_toPure_2187_);
                lean_dec_ref(v_toApplicative_2186_);
                v___x_2188_ = lean_apply_2(v_toPure_2187_, lean_box(0), v___x_2178_);
                return v___x_2188_;
            } else {
                let mut v___x_2189_: usize = 0;
                let mut v___x_2190_: usize = 0;
                let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
                v___x_2189_ = 0usize;
                v___x_2190_ = lean_usize_of_nat(v___x_2177_);
                v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
            v___x_2192_ = 0usize;
            v___x_2193_ = lean_usize_of_nat(v___x_2177_);
            v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
    mut v_x_2197_: *mut LeanObject,
    mut v_acc_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v___x_2199_ = lean_apply_2(v_f_2195_, v_a_2196_, v_acc_2198_);
    return v___x_2199_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg___lam__1(
    mut v_inst_2200_: *mut LeanObject,
    mut v___f_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_x_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_2200_, v___f_2201_, v_a_2202_, v___y_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_HashSet_Raw_forIn___redArg(
    mut v_inst_2206_: *mut LeanObject,
    mut v_f_2207_: *mut LeanObject,
    mut v_init_2208_: *mut LeanObject,
    mut v_b_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2210_ = lean_ctor_get(v_b_2209_, 1);
    lean_inc_ref(v_buckets_2210_);
    lean_dec_ref(v_b_2209_);
    v___f_2211_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2211_, 0, v_f_2207_);
    lean_inc_ref(v_inst_2206_);
    v___f_2212_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2212_, 0, v_inst_2206_);
    lean_closure_set(v___f_2212_, 1, v___f_2211_);
    v_sz_2213_ = lean_array_size(v_buckets_2210_);
    v___x_2214_ = 0usize;
    v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_00_u03b1_2216_: *mut LeanObject,
    mut v_m_2217_: *mut LeanObject,
    mut v_inst_2218_: *mut LeanObject,
    mut v_00_u03b2_2219_: *mut LeanObject,
    mut v_f_2220_: *mut LeanObject,
    mut v_init_2221_: *mut LeanObject,
    mut v_b_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2226_: usize = 0;
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2223_ = lean_ctor_get(v_b_2222_, 1);
    lean_inc_ref(v_buckets_2223_);
    lean_dec_ref(v_b_2222_);
    v___f_2224_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2224_, 0, v_f_2220_);
    lean_inc_ref(v_inst_2218_);
    v___f_2225_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2225_, 0, v_inst_2218_);
    lean_closure_set(v___f_2225_, 1, v___f_2224_);
    v_sz_2226_ = lean_array_size(v_buckets_2223_);
    v___x_2227_ = 0usize;
    v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_inst_2229_: *mut LeanObject,
    mut v_m_2230_: *mut LeanObject,
    mut v_f_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    v_buckets_2232_ = lean_ctor_get(v_m_2230_, 1);
    lean_inc_ref(v_buckets_2232_);
    lean_dec_ref(v_m_2230_);
    v___x_2233_ = lean_unsigned_to_nat(0);
    v___x_2234_ = lean_array_get_size(v_buckets_2232_);
    v___x_2235_ = lean_box(0);
    v___x_2236_ = lean_nat_dec_lt(v___x_2233_, v___x_2234_);
    if v___x_2236_ == 0 {
        let mut v_toApplicative_2237_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_buckets_2232_);
        lean_dec(v_f_2231_);
        v_toApplicative_2237_ = lean_ctor_get(v_inst_2229_, 0);
        lean_inc_ref(v_toApplicative_2237_);
        lean_dec_ref(v_inst_2229_);
        v_toPure_2238_ = lean_ctor_get(v_toApplicative_2237_, 1);
        lean_inc(v_toPure_2238_);
        lean_dec_ref(v_toApplicative_2237_);
        v___x_2239_ = lean_apply_2(v_toPure_2238_, lean_box(0), v___x_2235_);
        return v___x_2239_;
    } else {
        let mut v___f_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: u8 = 0;
        v___f_2240_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_2240_, 0, v_f_2231_);
        lean_inc_ref(v_inst_2229_);
        v___f_2241_ = lean_alloc_closure(
            l_Std_HashSet_Raw_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2241_, 0, v_inst_2229_);
        lean_closure_set(v___f_2241_, 1, v___f_2240_);
        v___x_2242_ = lean_nat_dec_le(v___x_2234_, v___x_2234_);
        if v___x_2242_ == 0 {
            if v___x_2236_ == 0 {
                let mut v_toApplicative_2243_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_2244_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_2241_);
                lean_dec_ref(v_buckets_2232_);
                v_toApplicative_2243_ = lean_ctor_get(v_inst_2229_, 0);
                lean_inc_ref(v_toApplicative_2243_);
                lean_dec_ref(v_inst_2229_);
                v_toPure_2244_ = lean_ctor_get(v_toApplicative_2243_, 1);
                lean_inc(v_toPure_2244_);
                lean_dec_ref(v_toApplicative_2243_);
                v___x_2245_ = lean_apply_2(v_toPure_2244_, lean_box(0), v___x_2235_);
                return v___x_2245_;
            } else {
                let mut v___x_2246_: usize = 0;
                let mut v___x_2247_: usize = 0;
                let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
                v___x_2246_ = 0usize;
                v___x_2247_ = lean_usize_of_nat(v___x_2234_);
                v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
            v___x_2249_ = 0usize;
            v___x_2250_ = lean_usize_of_nat(v___x_2234_);
            v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2253_: *mut LeanObject = core::ptr::null_mut();
    v___f_2253_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2253_, 0, v_inst_2252_);
    return v___f_2253_;
}
pub unsafe fn l_Std_HashSet_Raw_instForMOfMonad(
    mut v_00_u03b1_2254_: *mut LeanObject,
    mut v_m_2255_: *mut LeanObject,
    mut v_inst_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2257_: *mut LeanObject = core::ptr::null_mut();
    v___f_2257_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2257_, 0, v_inst_2256_);
    return v___f_2257_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(
    mut v_inst_2258_: *mut LeanObject,
    mut v_00_u03b2_2259_: *mut LeanObject,
    mut v_m_2260_: *mut LeanObject,
    mut v_init_2261_: *mut LeanObject,
    mut v_f_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2266_: usize = 0;
    let mut v___x_2267_: usize = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2263_ = lean_ctor_get(v_m_2260_, 1);
    lean_inc_ref(v_buckets_2263_);
    lean_dec_ref(v_m_2260_);
    v___f_2264_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2264_, 0, v_f_2262_);
    lean_inc_ref(v_inst_2258_);
    v___f_2265_ = lean_alloc_closure(
        l_Std_HashSet_Raw_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2265_, 0, v_inst_2258_);
    lean_closure_set(v___f_2265_, 1, v___f_2264_);
    v_sz_2266_ = lean_array_size(v_buckets_2263_);
    v___x_2267_ = 0usize;
    v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_inst_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2270_: *mut LeanObject = core::ptr::null_mut();
    v___f_2270_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2270_, 0, v_inst_2269_);
    return v___f_2270_;
}
pub unsafe fn l_Std_HashSet_Raw_instForInOfMonad(
    mut v_00_u03b1_2271_: *mut LeanObject,
    mut v_m_2272_: *mut LeanObject,
    mut v_inst_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2274_: *mut LeanObject = core::ptr::null_mut();
    v___f_2274_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2274_, 0, v_inst_2273_);
    return v___f_2274_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0(
    mut v_f_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_x_2277_: *mut LeanObject,
) -> u8 {
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: u8 = 0;
    v___x_2278_ = lean_apply_1(v_f_2275_, v_a_2276_);
    v___x_2279_ = (lean_unbox(v___x_2278_) as u8);
    return v___x_2279_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(
    mut v_f_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_x_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2283_: u8 = 0;
    let mut v_r_2284_: *mut LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_2280_, v_a_2281_, v_x_2282_);
    v_r_2284_ = lean_box((v_res_2283_) as usize);
    return v_r_2284_;
}
pub unsafe fn l_Std_HashSet_Raw_filter___redArg(
    mut v_f_2285_: *mut LeanObject,
    mut v_m_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    v_buckets_2287_ = lean_ctor_get(v_m_2286_, 1);
    v___x_2288_ = lean_unsigned_to_nat(0);
    v___x_2289_ = lean_array_get_size(v_buckets_2287_);
    v___x_2290_ = lean_nat_dec_lt(v___x_2288_, v___x_2289_);
    if v___x_2290_ == 0 {
        let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_m_2286_);
        lean_dec_ref(v_f_2285_);
        v___x_2291_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2291_;
    } else {
        let mut v___f_2292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
        v___f_2292_ = lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2292_, 0, v_f_2285_);
        v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2292_, v_m_2286_);
        return v___x_2293_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter(
    mut v_00_u03b1_2294_: *mut LeanObject,
    mut v_inst_2295_: *mut LeanObject,
    mut v_inst_2296_: *mut LeanObject,
    mut v_f_2297_: *mut LeanObject,
    mut v_m_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    v_buckets_2299_ = lean_ctor_get(v_m_2298_, 1);
    v___x_2300_ = lean_unsigned_to_nat(0);
    v___x_2301_ = lean_array_get_size(v_buckets_2299_);
    v___x_2302_ = lean_nat_dec_lt(v___x_2300_, v___x_2301_);
    if v___x_2302_ == 0 {
        let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_m_2298_);
        lean_dec_ref(v_f_2297_);
        v___x_2303_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
            core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
            _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
        );
        return v___x_2303_;
    } else {
        let mut v___f_2304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
        v___f_2304_ = lean_alloc_closure(
            l_Std_HashSet_Raw_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2304_, 0, v_f_2297_);
        v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2304_, v_m_2298_);
        return v___x_2305_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_filter___boxed(
    mut v_00_u03b1_2306_: *mut LeanObject,
    mut v_inst_2307_: *mut LeanObject,
    mut v_inst_2308_: *mut LeanObject,
    mut v_f_2309_: *mut LeanObject,
    mut v_m_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2311_: *mut LeanObject = core::ptr::null_mut();
    v_res_2311_ = l_Std_HashSet_Raw_filter(
        v_00_u03b1_2306_,
        v_inst_2307_,
        v_inst_2308_,
        v_f_2309_,
        v_m_2310_,
    );
    lean_dec_ref(v_inst_2308_);
    lean_dec_ref(v_inst_2307_);
    return v_res_2311_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__0(
    mut v_x1_2312_: *mut LeanObject,
    mut v_x2_2313_: *mut LeanObject,
    mut v_x3_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = lean_array_push(v_x1_2312_, v_x2_2313_);
    return v___x_2315_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg___lam__1(
    mut v___x_2316_: *mut LeanObject,
    mut v___f_2317_: *mut LeanObject,
    mut v_acc_2318_: *mut LeanObject,
    mut v_l_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2320_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_2316_,
        v___f_2317_,
        v_acc_2318_,
        v_l_2319_,
    );
    return v___x_2320_;
}
pub unsafe fn l_Std_HashSet_Raw_toArray___redArg(
    mut v_m_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    v_size_2326_ = lean_ctor_get(v_m_2325_, 0);
    lean_inc(v_size_2326_);
    v_buckets_2327_ = lean_ctor_get(v_m_2325_, 1);
    lean_inc_ref(v_buckets_2327_);
    lean_dec_ref(v_m_2325_);
    v___x_2328_ = lean_mk_empty_array_with_capacity(v_size_2326_);
    lean_dec(v_size_2326_);
    v___x_2329_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2330_ = lean_unsigned_to_nat(0);
    v___x_2331_ = lean_array_get_size(v_buckets_2327_);
    v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
    if v___x_2332_ == 0 {
        lean_dec_ref(v_buckets_2327_);
        return v___x_2328_;
    } else {
        let mut v___f_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        v___f_2333_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2334_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
        if v___x_2334_ == 0 {
            if v___x_2332_ == 0 {
                lean_dec_ref(v_buckets_2327_);
                return v___x_2328_;
            } else {
                let mut v___x_2335_: usize = 0;
                let mut v___x_2336_: usize = 0;
                let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
                v___x_2335_ = 0usize;
                v___x_2336_ = lean_usize_of_nat(v___x_2331_);
                v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
            v___x_2338_ = 0usize;
            v___x_2339_ = lean_usize_of_nat(v___x_2331_);
            v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_2341_: *mut LeanObject,
    mut v_m_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: u8 = 0;
    v_size_2343_ = lean_ctor_get(v_m_2342_, 0);
    lean_inc(v_size_2343_);
    v_buckets_2344_ = lean_ctor_get(v_m_2342_, 1);
    lean_inc_ref(v_buckets_2344_);
    lean_dec_ref(v_m_2342_);
    v___x_2345_ = lean_mk_empty_array_with_capacity(v_size_2343_);
    lean_dec(v_size_2343_);
    v___x_2346_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v___x_2347_ = lean_unsigned_to_nat(0);
    v___x_2348_ = lean_array_get_size(v_buckets_2344_);
    v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
    if v___x_2349_ == 0 {
        lean_dec_ref(v_buckets_2344_);
        return v___x_2345_;
    } else {
        let mut v___f_2350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: u8 = 0;
        v___f_2350_ = l_Std_HashSet_Raw_toArray___redArg___closed__1;
        v___x_2351_ = lean_nat_dec_le(v___x_2348_, v___x_2348_);
        if v___x_2351_ == 0 {
            if v___x_2349_ == 0 {
                lean_dec_ref(v_buckets_2344_);
                return v___x_2345_;
            } else {
                let mut v___x_2352_: usize = 0;
                let mut v___x_2353_: usize = 0;
                let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
                v___x_2352_ = 0usize;
                v___x_2353_ = lean_usize_of_nat(v___x_2348_);
                v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
            v___x_2355_ = 0usize;
            v___x_2356_ = lean_usize_of_nat(v___x_2348_);
            v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_2358_: *mut LeanObject,
    mut v_inst_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_b_2361_: *mut LeanObject,
    mut v_acc_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v_r_2363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_2358_,
        v_inst_2359_,
        v_acc_2362_,
        v_a_2360_,
        v_b_2361_,
    );
    v___x_2364_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2364_, 0, v_r_2363_);
    return v___x_2364_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg___lam__1(
    mut v___x_2365_: *mut LeanObject,
    mut v___f_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_x_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2370_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_2365_, v___f_2366_, v_a_2367_, v___y_2369_);
    return v___x_2370_;
}
pub unsafe fn l_Std_HashSet_Raw_union___redArg(
    mut v_inst_2373_: *mut LeanObject,
    mut v_inst_2374_: *mut LeanObject,
    mut v_m_u2081_2375_: *mut LeanObject,
    mut v_m_u2082_2376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    v_size_2377_ = lean_ctor_get(v_m_u2081_2375_, 0);
    v_buckets_2378_ = lean_ctor_get(v_m_u2081_2375_, 1);
    v___x_2379_ = lean_unsigned_to_nat(0);
    v___x_2380_ = lean_array_get_size(v_buckets_2378_);
    v___x_2381_ = lean_nat_dec_lt(v___x_2379_, v___x_2380_);
    if v___x_2381_ == 0 {
        lean_dec_ref(v_m_u2081_2375_);
        lean_dec_ref(v_inst_2374_);
        lean_dec_ref(v_inst_2373_);
        return v_m_u2082_2376_;
    } else {
        let mut v_size_2382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_buckets_2383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: u8 = 0;
        v_size_2382_ = lean_ctor_get(v_m_u2082_2376_, 0);
        v_buckets_2383_ = lean_ctor_get(v_m_u2082_2376_, 1);
        v___x_2384_ = lean_array_get_size(v_buckets_2383_);
        v___x_2385_ = lean_nat_dec_lt(v___x_2379_, v___x_2384_);
        if v___x_2385_ == 0 {
            lean_dec_ref(v_m_u2082_2376_);
            lean_dec_ref(v_inst_2374_);
            lean_dec_ref(v_inst_2373_);
            return v_m_u2081_2375_;
        } else {
            let mut v___x_2386_: u8 = 0;
            v___x_2386_ = lean_nat_dec_le(v_size_2377_, v_size_2382_);
            if v___x_2386_ == 0 {
                let mut v___f_2387_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___f_2389_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_2391_: *mut LeanObject = core::ptr::null_mut();
                let mut v_sz_2392_: usize = 0;
                let mut v___x_2393_: usize = 0;
                let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_buckets_2378_);
                lean_dec_ref(v_m_u2081_2375_);
                v___f_2389_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2389_, 0, v_inst_2373_);
                lean_closure_set(v___f_2389_, 1, v_inst_2374_);
                v___x_2390_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2391_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2391_, 0, v___x_2390_);
                lean_closure_set(v___f_2391_, 1, v___f_2389_);
                v_sz_2392_ = lean_array_size(v_buckets_2378_);
                v___x_2393_ = 0usize;
                v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_00_u03b1_2395_: *mut LeanObject,
    mut v_inst_2396_: *mut LeanObject,
    mut v_inst_2397_: *mut LeanObject,
    mut v_m_u2081_2398_: *mut LeanObject,
    mut v_m_u2082_2399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: u8 = 0;
    v_size_2400_ = lean_ctor_get(v_m_u2081_2398_, 0);
    v_buckets_2401_ = lean_ctor_get(v_m_u2081_2398_, 1);
    v___x_2402_ = lean_unsigned_to_nat(0);
    v___x_2403_ = lean_array_get_size(v_buckets_2401_);
    v___x_2404_ = lean_nat_dec_lt(v___x_2402_, v___x_2403_);
    if v___x_2404_ == 0 {
        lean_dec_ref(v_m_u2081_2398_);
        lean_dec_ref(v_inst_2397_);
        lean_dec_ref(v_inst_2396_);
        return v_m_u2082_2399_;
    } else {
        let mut v_size_2405_: *mut LeanObject = core::ptr::null_mut();
        let mut v_buckets_2406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: u8 = 0;
        v_size_2405_ = lean_ctor_get(v_m_u2082_2399_, 0);
        v_buckets_2406_ = lean_ctor_get(v_m_u2082_2399_, 1);
        v___x_2407_ = lean_array_get_size(v_buckets_2406_);
        v___x_2408_ = lean_nat_dec_lt(v___x_2402_, v___x_2407_);
        if v___x_2408_ == 0 {
            lean_dec_ref(v_m_u2082_2399_);
            lean_dec_ref(v_inst_2397_);
            lean_dec_ref(v_inst_2396_);
            return v_m_u2081_2398_;
        } else {
            let mut v___x_2409_: u8 = 0;
            v___x_2409_ = lean_nat_dec_le(v_size_2400_, v_size_2405_);
            if v___x_2409_ == 0 {
                let mut v___f_2410_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___f_2412_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_2414_: *mut LeanObject = core::ptr::null_mut();
                let mut v_sz_2415_: usize = 0;
                let mut v___x_2416_: usize = 0;
                let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_buckets_2401_);
                lean_dec_ref(v_m_u2081_2398_);
                v___f_2412_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2412_, 0, v_inst_2396_);
                lean_closure_set(v___f_2412_, 1, v_inst_2397_);
                v___x_2413_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v___f_2414_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_union___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2414_, 0, v___x_2413_);
                lean_closure_set(v___f_2414_, 1, v___f_2412_);
                v_sz_2415_ = lean_array_size(v_buckets_2401_);
                v___x_2416_ = 0usize;
                v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_2418_: *mut LeanObject,
    mut v_inst_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    v___x_2420_ = lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2420_, 0, lean_box(0));
    lean_closure_set(v___x_2420_, 1, v_inst_2418_);
    lean_closure_set(v___x_2420_, 2, v_inst_2419_);
    return v___x_2420_;
}
pub unsafe fn l_Std_HashSet_Raw_instUnionOfBEqOfHashable(
    mut v_00_u03b1_2421_: *mut LeanObject,
    mut v_inst_2422_: *mut LeanObject,
    mut v_inst_2423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    v___x_2424_ = lean_alloc_closure(l_Std_HashSet_Raw_union as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2424_, 0, lean_box(0));
    lean_closure_set(v___x_2424_, 1, v_inst_2422_);
    lean_closure_set(v___x_2424_, 2, v_inst_2423_);
    return v___x_2424_;
}
pub unsafe fn l_Std_HashSet_Raw_inter___redArg(
    mut v_inst_2425_: *mut LeanObject,
    mut v_inst_2426_: *mut LeanObject,
    mut v_m_u2081_2427_: *mut LeanObject,
    mut v_m_u2082_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    v_buckets_2429_ = lean_ctor_get(v_m_u2081_2427_, 1);
    v___x_2430_ = lean_unsigned_to_nat(0);
    v___x_2431_ = lean_array_get_size(v_buckets_2429_);
    v___x_2432_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
    if v___x_2432_ == 0 {
        lean_dec_ref(v_m_u2081_2427_);
        lean_dec_ref(v_inst_2426_);
        lean_dec_ref(v_inst_2425_);
        return v_m_u2082_2428_;
    } else {
        let mut v_buckets_2433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2435_: u8 = 0;
        v_buckets_2433_ = lean_ctor_get(v_m_u2082_2428_, 1);
        v___x_2434_ = lean_array_get_size(v_buckets_2433_);
        v___x_2435_ = lean_nat_dec_lt(v___x_2430_, v___x_2434_);
        if v___x_2435_ == 0 {
            lean_dec_ref(v_m_u2082_2428_);
            lean_dec_ref(v_inst_2426_);
            lean_dec_ref(v_inst_2425_);
            return v_m_u2081_2427_;
        } else {
            let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2437_: *mut LeanObject,
    mut v_inst_2438_: *mut LeanObject,
    mut v_inst_2439_: *mut LeanObject,
    mut v_m_u2081_2440_: *mut LeanObject,
    mut v_m_u2082_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    v_buckets_2442_ = lean_ctor_get(v_m_u2081_2440_, 1);
    v___x_2443_ = lean_unsigned_to_nat(0);
    v___x_2444_ = lean_array_get_size(v_buckets_2442_);
    v___x_2445_ = lean_nat_dec_lt(v___x_2443_, v___x_2444_);
    if v___x_2445_ == 0 {
        lean_dec_ref(v_m_u2081_2440_);
        lean_dec_ref(v_inst_2439_);
        lean_dec_ref(v_inst_2438_);
        return v_m_u2082_2441_;
    } else {
        let mut v_buckets_2446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: u8 = 0;
        v_buckets_2446_ = lean_ctor_get(v_m_u2082_2441_, 1);
        v___x_2447_ = lean_array_get_size(v_buckets_2446_);
        v___x_2448_ = lean_nat_dec_lt(v___x_2443_, v___x_2447_);
        if v___x_2448_ == 0 {
            lean_dec_ref(v_m_u2082_2441_);
            lean_dec_ref(v_inst_2439_);
            lean_dec_ref(v_inst_2438_);
            return v_m_u2081_2440_;
        } else {
            let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2450_: *mut LeanObject,
    mut v_inst_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2452_, 0, lean_box(0));
    lean_closure_set(v___x_2452_, 1, v_inst_2450_);
    lean_closure_set(v___x_2452_, 2, v_inst_2451_);
    return v___x_2452_;
}
pub unsafe fn l_Std_HashSet_Raw_instInterOfBEqOfHashable(
    mut v_00_u03b1_2453_: *mut LeanObject,
    mut v_inst_2454_: *mut LeanObject,
    mut v_inst_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    v___x_2456_ = lean_alloc_closure(l_Std_HashSet_Raw_inter as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2456_, 0, lean_box(0));
    lean_closure_set(v___x_2456_, 1, v_inst_2454_);
    lean_closure_set(v___x_2456_, 2, v_inst_2455_);
    return v___x_2456_;
}
pub unsafe fn _init_l_Std_HashSet_Raw_beq___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2458_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2458_, 0, v___x_2457_);
    return v___f_2458_;
}
pub unsafe fn l_Std_HashSet_Raw_beq___redArg(
    mut v_inst_2459_: *mut LeanObject,
    mut v_inst_2460_: *mut LeanObject,
    mut v_m_u2081_2461_: *mut LeanObject,
    mut v_m_u2082_2462_: *mut LeanObject,
) -> u8 {
    let mut v___f_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    v___f_2463_ = lean_obj_once(
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
    mut v_inst_2465_: *mut LeanObject,
    mut v_inst_2466_: *mut LeanObject,
    mut v_m_u2081_2467_: *mut LeanObject,
    mut v_m_u2082_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2469_: u8 = 0;
    let mut v_r_2470_: *mut LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Std_HashSet_Raw_beq___redArg(
        v_inst_2465_,
        v_inst_2466_,
        v_m_u2081_2467_,
        v_m_u2082_2468_,
    );
    v_r_2470_ = lean_box((v_res_2469_) as usize);
    return v_r_2470_;
}
pub unsafe fn l_Std_HashSet_Raw_beq(
    mut v_00_u03b1_2471_: *mut LeanObject,
    mut v_inst_2472_: *mut LeanObject,
    mut v_inst_2473_: *mut LeanObject,
    mut v_m_u2081_2474_: *mut LeanObject,
    mut v_m_u2082_2475_: *mut LeanObject,
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
    mut v_00_u03b1_2477_: *mut LeanObject,
    mut v_inst_2478_: *mut LeanObject,
    mut v_inst_2479_: *mut LeanObject,
    mut v_m_u2081_2480_: *mut LeanObject,
    mut v_m_u2082_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2482_: u8 = 0;
    let mut v_r_2483_: *mut LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_HashSet_Raw_beq(
        v_00_u03b1_2477_,
        v_inst_2478_,
        v_inst_2479_,
        v_m_u2081_2480_,
        v_m_u2082_2481_,
    );
    v_r_2483_ = lean_box((v_res_2482_) as usize);
    return v_r_2483_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable___redArg(
    mut v_inst_2484_: *mut LeanObject,
    mut v_inst_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2486_, 0, lean_box(0));
    lean_closure_set(v___x_2486_, 1, v_inst_2484_);
    lean_closure_set(v___x_2486_, 2, v_inst_2485_);
    return v___x_2486_;
}
pub unsafe fn l_Std_HashSet_Raw_instBEqOfHashable(
    mut v_00_u03b1_2487_: *mut LeanObject,
    mut v_inst_2488_: *mut LeanObject,
    mut v_inst_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    v___x_2490_ = lean_alloc_closure(
        l_Std_HashSet_Raw_beq___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_2490_, 0, lean_box(0));
    lean_closure_set(v___x_2490_, 1, v_inst_2488_);
    lean_closure_set(v___x_2490_, 2, v_inst_2489_);
    return v___x_2490_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg___lam__0(
    mut v_inst_2491_: *mut LeanObject,
    mut v_inst_2492_: *mut LeanObject,
    mut v_m_u2082_2493_: *mut LeanObject,
    mut v___x_2494_: u8,
    mut v_k_2495_: *mut LeanObject,
    mut v_x_2496_: *mut LeanObject,
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
    mut v_inst_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_m_u2082_2501_: *mut LeanObject,
    mut v___x_2502_: *mut LeanObject,
    mut v_k_2503_: *mut LeanObject,
    mut v_x_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_97__boxed_2505_: u8 = 0;
    let mut v_res_2506_: u8 = 0;
    let mut v_r_2507_: *mut LeanObject = core::ptr::null_mut();
    v___x_97__boxed_2505_ = (lean_unbox(v___x_2502_) as u8);
    v_res_2506_ = l_Std_HashSet_Raw_diff___redArg___lam__0(
        v_inst_2499_,
        v_inst_2500_,
        v_m_u2082_2501_,
        v___x_97__boxed_2505_,
        v_k_2503_,
        v_x_2504_,
    );
    lean_dec_ref(v_m_u2082_2501_);
    v_r_2507_ = lean_box((v_res_2506_) as usize);
    return v_r_2507_;
}
pub unsafe fn l_Std_HashSet_Raw_diff___redArg(
    mut v_inst_2508_: *mut LeanObject,
    mut v_inst_2509_: *mut LeanObject,
    mut v_m_u2081_2510_: *mut LeanObject,
    mut v_m_u2082_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    v_size_2512_ = lean_ctor_get(v_m_u2081_2510_, 0);
    v_buckets_2513_ = lean_ctor_get(v_m_u2081_2510_, 1);
    v___x_2514_ = lean_unsigned_to_nat(0);
    v___x_2515_ = lean_array_get_size(v_buckets_2513_);
    v___x_2516_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
    if v___x_2516_ == 0 {
        lean_dec_ref(v_m_u2081_2510_);
        lean_dec_ref(v_inst_2509_);
        lean_dec_ref(v_inst_2508_);
        return v_m_u2082_2511_;
    } else {
        let mut v_size_2517_: *mut LeanObject = core::ptr::null_mut();
        let mut v_buckets_2518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: u8 = 0;
        v_size_2517_ = lean_ctor_get(v_m_u2082_2511_, 0);
        v_buckets_2518_ = lean_ctor_get(v_m_u2082_2511_, 1);
        v___x_2519_ = lean_array_get_size(v_buckets_2518_);
        v___x_2520_ = lean_nat_dec_lt(v___x_2514_, v___x_2519_);
        if v___x_2520_ == 0 {
            lean_dec_ref(v_m_u2082_2511_);
            lean_dec_ref(v_inst_2509_);
            lean_dec_ref(v_inst_2508_);
            return v_m_u2081_2510_;
        } else {
            let mut v___x_2521_: u8 = 0;
            v___x_2521_ = lean_nat_dec_le(v_size_2512_, v_size_2517_);
            if v___x_2521_ == 0 {
                let mut v___f_2522_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_2525_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
                v___x_2524_ = lean_box((v___x_2521_) as usize);
                v___f_2525_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_2525_, 0, v_inst_2508_);
                lean_closure_set(v___f_2525_, 1, v_inst_2509_);
                lean_closure_set(v___f_2525_, 2, v_m_u2082_2511_);
                lean_closure_set(v___f_2525_, 3, v___x_2524_);
                v___x_2526_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2525_, v_m_u2081_2510_);
                return v___x_2526_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_diff(
    mut v_00_u03b1_2527_: *mut LeanObject,
    mut v_inst_2528_: *mut LeanObject,
    mut v_inst_2529_: *mut LeanObject,
    mut v_m_u2081_2530_: *mut LeanObject,
    mut v_m_u2082_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    v_size_2532_ = lean_ctor_get(v_m_u2081_2530_, 0);
    v_buckets_2533_ = lean_ctor_get(v_m_u2081_2530_, 1);
    v___x_2534_ = lean_unsigned_to_nat(0);
    v___x_2535_ = lean_array_get_size(v_buckets_2533_);
    v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2535_);
    if v___x_2536_ == 0 {
        lean_dec_ref(v_m_u2081_2530_);
        lean_dec_ref(v_inst_2529_);
        lean_dec_ref(v_inst_2528_);
        return v_m_u2082_2531_;
    } else {
        let mut v_size_2537_: *mut LeanObject = core::ptr::null_mut();
        let mut v_buckets_2538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: u8 = 0;
        v_size_2537_ = lean_ctor_get(v_m_u2082_2531_, 0);
        v_buckets_2538_ = lean_ctor_get(v_m_u2082_2531_, 1);
        v___x_2539_ = lean_array_get_size(v_buckets_2538_);
        v___x_2540_ = lean_nat_dec_lt(v___x_2534_, v___x_2539_);
        if v___x_2540_ == 0 {
            lean_dec_ref(v_m_u2082_2531_);
            lean_dec_ref(v_inst_2529_);
            lean_dec_ref(v_inst_2528_);
            return v_m_u2081_2530_;
        } else {
            let mut v___x_2541_: u8 = 0;
            v___x_2541_ = lean_nat_dec_le(v_size_2532_, v_size_2537_);
            if v___x_2541_ == 0 {
                let mut v___f_2542_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_2545_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
                v___x_2544_ = lean_box((v___x_2541_) as usize);
                v___f_2545_ = lean_alloc_closure(
                    l_Std_HashSet_Raw_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_2545_, 0, v_inst_2528_);
                lean_closure_set(v___f_2545_, 1, v_inst_2529_);
                lean_closure_set(v___f_2545_, 2, v_m_u2082_2531_);
                lean_closure_set(v___f_2545_, 3, v___x_2544_);
                v___x_2546_ =
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2545_, v_m_u2081_2530_);
                return v___x_2546_;
            }
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(
    mut v_inst_2547_: *mut LeanObject,
    mut v_inst_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    v___x_2549_ = lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2549_, 0, lean_box(0));
    lean_closure_set(v___x_2549_, 1, v_inst_2547_);
    lean_closure_set(v___x_2549_, 2, v_inst_2548_);
    return v___x_2549_;
}
pub unsafe fn l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(
    mut v_00_u03b1_2550_: *mut LeanObject,
    mut v_inst_2551_: *mut LeanObject,
    mut v_inst_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = lean_alloc_closure(l_Std_HashSet_Raw_diff as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2553_, 0, lean_box(0));
    lean_closure_set(v___x_2553_, 1, v_inst_2551_);
    lean_closure_set(v___x_2553_, 2, v_inst_2552_);
    return v___x_2553_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0(
    mut v_p_2554_: *mut LeanObject,
    mut v___x_2555_: *mut LeanObject,
    mut v___x_2556_: *mut LeanObject,
    mut v_a_2557_: *mut LeanObject,
    mut v_b_2558_: *mut LeanObject,
    mut v_acc_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    v___x_2560_ = lean_apply_1(v_p_2554_, v_a_2557_);
    v___x_2561_ = (lean_unbox(v___x_2560_) as u8);
    if v___x_2561_ == 0 {
        let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2556_);
        v___x_2562_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2562_, 0, v___x_2560_);
        v___x_2563_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2563_, 0, v___x_2562_);
        lean_ctor_set(v___x_2563_, 1, v___x_2555_);
        v___x_2564_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2564_, 0, v___x_2563_);
        return v___x_2564_;
    } else {
        let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
        v___x_2565_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2565_, 0, v___x_2556_);
        return v___x_2565_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__0___boxed(
    mut v_p_2566_: *mut LeanObject,
    mut v___x_2567_: *mut LeanObject,
    mut v___x_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
    mut v_b_2570_: *mut LeanObject,
    mut v_acc_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2572_: *mut LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_HashSet_Raw_all___redArg___lam__0(
        v_p_2566_,
        v___x_2567_,
        v___x_2568_,
        v_a_2569_,
        v_b_2570_,
        v_acc_2571_,
    );
    lean_dec_ref(v_acc_2571_);
    return v_res_2572_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___lam__1(
    mut v___x_2573_: *mut LeanObject,
    mut v___f_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_x_2576_: *mut LeanObject,
    mut v___y_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_2573_, v___f_2574_, v_a_2575_, v___y_2577_);
    return v___x_2578_;
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg(
    mut v_m_2582_: *mut LeanObject,
    mut v_p_2583_: *mut LeanObject,
) -> u8 {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2590_: usize = 0;
    let mut v___x_2591_: usize = 0;
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2585_ = lean_ctor_get(v_m_2582_, 1);
    lean_inc_ref(v_buckets_2585_);
    lean_dec_ref(v_m_2582_);
    v___x_2586_ = lean_box(0);
    v___x_2587_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2588_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2588_, 0, v_p_2583_);
    lean_closure_set(v___f_2588_, 1, v___x_2586_);
    lean_closure_set(v___f_2588_, 2, v___x_2587_);
    v___f_2589_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2589_, 0, v___x_2584_);
    lean_closure_set(v___f_2589_, 1, v___f_2588_);
    v_sz_2590_ = lean_array_size(v_buckets_2585_);
    v___x_2591_ = 0usize;
    v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2584_,
        v_buckets_2585_,
        v___f_2589_,
        v_sz_2590_,
        v___x_2591_,
        v___x_2587_,
    );
    v_fst_2593_ = lean_ctor_get(v___x_2592_, 0);
    lean_inc(v_fst_2593_);
    lean_dec(v___x_2592_);
    if lean_obj_tag(v_fst_2593_) == 0 {
        let mut v___x_2594_: u8 = 0;
        v___x_2594_ = 1;
        return v___x_2594_;
    } else {
        let mut v_val_2595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2596_: u8 = 0;
        v_val_2595_ = lean_ctor_get(v_fst_2593_, 0);
        lean_inc(v_val_2595_);
        lean_dec_ref_known(v_fst_2593_, 1);
        v___x_2596_ = (lean_unbox(v_val_2595_) as u8);
        lean_dec(v_val_2595_);
        return v___x_2596_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___redArg___boxed(
    mut v_m_2597_: *mut LeanObject,
    mut v_p_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2599_: u8 = 0;
    let mut v_r_2600_: *mut LeanObject = core::ptr::null_mut();
    v_res_2599_ = l_Std_HashSet_Raw_all___redArg(v_m_2597_, v_p_2598_);
    v_r_2600_ = lean_box((v_res_2599_) as usize);
    return v_r_2600_;
}
pub unsafe fn l_Std_HashSet_Raw_all(
    mut v_00_u03b1_2601_: *mut LeanObject,
    mut v_m_2602_: *mut LeanObject,
    mut v_p_2603_: *mut LeanObject,
) -> u8 {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2605_ = lean_ctor_get(v_m_2602_, 1);
    lean_inc_ref(v_buckets_2605_);
    lean_dec_ref(v_m_2602_);
    v___x_2606_ = lean_box(0);
    v___x_2607_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2608_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2608_, 0, v_p_2603_);
    lean_closure_set(v___f_2608_, 1, v___x_2606_);
    lean_closure_set(v___f_2608_, 2, v___x_2607_);
    v___f_2609_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2609_, 0, v___x_2604_);
    lean_closure_set(v___f_2609_, 1, v___f_2608_);
    v_sz_2610_ = lean_array_size(v_buckets_2605_);
    v___x_2611_ = 0usize;
    v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2604_,
        v_buckets_2605_,
        v___f_2609_,
        v_sz_2610_,
        v___x_2611_,
        v___x_2607_,
    );
    v_fst_2613_ = lean_ctor_get(v___x_2612_, 0);
    lean_inc(v_fst_2613_);
    lean_dec(v___x_2612_);
    if lean_obj_tag(v_fst_2613_) == 0 {
        let mut v___x_2614_: u8 = 0;
        v___x_2614_ = 1;
        return v___x_2614_;
    } else {
        let mut v_val_2615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: u8 = 0;
        v_val_2615_ = lean_ctor_get(v_fst_2613_, 0);
        lean_inc(v_val_2615_);
        lean_dec_ref_known(v_fst_2613_, 1);
        v___x_2616_ = (lean_unbox(v_val_2615_) as u8);
        lean_dec(v_val_2615_);
        return v___x_2616_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_all___boxed(
    mut v_00_u03b1_2617_: *mut LeanObject,
    mut v_m_2618_: *mut LeanObject,
    mut v_p_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Std_HashSet_Raw_all(v_00_u03b1_2617_, v_m_2618_, v_p_2619_);
    v_r_2621_ = lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0(
    mut v_p_2622_: *mut LeanObject,
    mut v___x_2623_: *mut LeanObject,
    mut v___x_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_b_2626_: *mut LeanObject,
    mut v_acc_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    v___x_2628_ = lean_apply_1(v_p_2622_, v_a_2625_);
    v___x_2629_ = (lean_unbox(v___x_2628_) as u8);
    if v___x_2629_ == 0 {
        let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
        v___x_2630_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2630_, 0, v___x_2623_);
        return v___x_2630_;
    } else {
        let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2623_);
        v___x_2631_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2631_, 0, v___x_2628_);
        v___x_2632_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2632_, 0, v___x_2631_);
        lean_ctor_set(v___x_2632_, 1, v___x_2624_);
        v___x_2633_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2633_, 0, v___x_2632_);
        return v___x_2633_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___lam__0___boxed(
    mut v_p_2634_: *mut LeanObject,
    mut v___x_2635_: *mut LeanObject,
    mut v___x_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
    mut v_b_2638_: *mut LeanObject,
    mut v_acc_2639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2640_: *mut LeanObject = core::ptr::null_mut();
    v_res_2640_ = l_Std_HashSet_Raw_any___redArg___lam__0(
        v_p_2634_,
        v___x_2635_,
        v___x_2636_,
        v_a_2637_,
        v_b_2638_,
        v_acc_2639_,
    );
    lean_dec_ref(v_acc_2639_);
    return v_res_2640_;
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg(
    mut v_m_2641_: *mut LeanObject,
    mut v_p_2642_: *mut LeanObject,
) -> u8 {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2649_: usize = 0;
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2643_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2644_ = lean_ctor_get(v_m_2641_, 1);
    lean_inc_ref(v_buckets_2644_);
    lean_dec_ref(v_m_2641_);
    v___x_2645_ = lean_box(0);
    v___x_2646_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2647_ = lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2647_, 0, v_p_2642_);
    lean_closure_set(v___f_2647_, 1, v___x_2646_);
    lean_closure_set(v___f_2647_, 2, v___x_2645_);
    v___f_2648_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2648_, 0, v___x_2643_);
    lean_closure_set(v___f_2648_, 1, v___f_2647_);
    v_sz_2649_ = lean_array_size(v_buckets_2644_);
    v___x_2650_ = 0usize;
    v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2643_,
        v_buckets_2644_,
        v___f_2648_,
        v_sz_2649_,
        v___x_2650_,
        v___x_2646_,
    );
    v_fst_2652_ = lean_ctor_get(v___x_2651_, 0);
    lean_inc(v_fst_2652_);
    lean_dec(v___x_2651_);
    if lean_obj_tag(v_fst_2652_) == 0 {
        let mut v___x_2653_: u8 = 0;
        v___x_2653_ = 0;
        return v___x_2653_;
    } else {
        let mut v_val_2654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: u8 = 0;
        v_val_2654_ = lean_ctor_get(v_fst_2652_, 0);
        lean_inc(v_val_2654_);
        lean_dec_ref_known(v_fst_2652_, 1);
        v___x_2655_ = (lean_unbox(v_val_2654_) as u8);
        lean_dec(v_val_2654_);
        return v___x_2655_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___redArg___boxed(
    mut v_m_2656_: *mut LeanObject,
    mut v_p_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2658_: u8 = 0;
    let mut v_r_2659_: *mut LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Std_HashSet_Raw_any___redArg(v_m_2656_, v_p_2657_);
    v_r_2659_ = lean_box((v_res_2658_) as usize);
    return v_r_2659_;
}
pub unsafe fn l_Std_HashSet_Raw_any(
    mut v_00_u03b1_2660_: *mut LeanObject,
    mut v_m_2661_: *mut LeanObject,
    mut v_p_2662_: *mut LeanObject,
) -> u8 {
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2669_: usize = 0;
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2672_: *mut LeanObject = core::ptr::null_mut();
    v___x_2663_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
    v_buckets_2664_ = lean_ctor_get(v_m_2661_, 1);
    lean_inc_ref(v_buckets_2664_);
    lean_dec_ref(v_m_2661_);
    v___x_2665_ = lean_box(0);
    v___x_2666_ = l_Std_HashSet_Raw_all___redArg___closed__0;
    v___f_2667_ = lean_alloc_closure(
        l_Std_HashSet_Raw_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_2667_, 0, v_p_2662_);
    lean_closure_set(v___f_2667_, 1, v___x_2666_);
    lean_closure_set(v___f_2667_, 2, v___x_2665_);
    v___f_2668_ = lean_alloc_closure(
        l_Std_HashSet_Raw_all___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2668_, 0, v___x_2663_);
    lean_closure_set(v___f_2668_, 1, v___f_2667_);
    v_sz_2669_ = lean_array_size(v_buckets_2664_);
    v___x_2670_ = 0usize;
    v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2663_,
        v_buckets_2664_,
        v___f_2668_,
        v_sz_2669_,
        v___x_2670_,
        v___x_2666_,
    );
    v_fst_2672_ = lean_ctor_get(v___x_2671_, 0);
    lean_inc(v_fst_2672_);
    lean_dec(v___x_2671_);
    if lean_obj_tag(v_fst_2672_) == 0 {
        let mut v___x_2673_: u8 = 0;
        v___x_2673_ = 0;
        return v___x_2673_;
    } else {
        let mut v_val_2674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: u8 = 0;
        v_val_2674_ = lean_ctor_get(v_fst_2672_, 0);
        lean_inc(v_val_2674_);
        lean_dec_ref_known(v_fst_2672_, 1);
        v___x_2675_ = (lean_unbox(v_val_2674_) as u8);
        lean_dec(v_val_2674_);
        return v___x_2675_;
    }
}
pub unsafe fn l_Std_HashSet_Raw_any___boxed(
    mut v_00_u03b1_2676_: *mut LeanObject,
    mut v_m_2677_: *mut LeanObject,
    mut v_p_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2679_: u8 = 0;
    let mut v_r_2680_: *mut LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Std_HashSet_Raw_any(v_00_u03b1_2676_, v_m_2677_, v_p_2678_);
    v_r_2680_ = lean_box((v_res_2679_) as usize);
    return v_r_2680_;
}
pub unsafe fn l_Std_HashSet_Raw_insertMany___redArg(
    mut v_inst_2681_: *mut LeanObject,
    mut v_inst_2682_: *mut LeanObject,
    mut v_inst_2683_: *mut LeanObject,
    mut v_m_2684_: *mut LeanObject,
    mut v_l_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: u8 = 0;
    v_buckets_2686_ = lean_ctor_get(v_m_2684_, 1);
    v___x_2687_ = lean_unsigned_to_nat(0);
    v___x_2688_ = lean_array_get_size(v_buckets_2686_);
    v___x_2689_ = lean_nat_dec_lt(v___x_2687_, v___x_2688_);
    if v___x_2689_ == 0 {
        lean_dec(v_l_2685_);
        lean_dec(v_inst_2683_);
        lean_dec_ref(v_inst_2682_);
        lean_dec_ref(v_inst_2681_);
        return v_m_2684_;
    } else {
        let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2691_: *mut LeanObject,
    mut v_inst_2692_: *mut LeanObject,
    mut v_inst_2693_: *mut LeanObject,
    mut v_00_u03c1_2694_: *mut LeanObject,
    mut v_inst_2695_: *mut LeanObject,
    mut v_m_2696_: *mut LeanObject,
    mut v_l_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    v_buckets_2698_ = lean_ctor_get(v_m_2696_, 1);
    v___x_2699_ = lean_unsigned_to_nat(0);
    v___x_2700_ = lean_array_get_size(v_buckets_2698_);
    v___x_2701_ = lean_nat_dec_lt(v___x_2699_, v___x_2700_);
    if v___x_2701_ == 0 {
        lean_dec(v_l_2697_);
        lean_dec(v_inst_2695_);
        lean_dec_ref(v_inst_2693_);
        lean_dec_ref(v_inst_2692_);
        return v_m_2696_;
    } else {
        let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2707_: *mut LeanObject,
    mut v_inst_2708_: *mut LeanObject,
    mut v_l_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    v___x_2710_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2711_ = lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2711_ == 0 {
        lean_dec_ref(v_l_2709_);
        lean_dec_ref(v_inst_2708_);
        lean_dec_ref(v_inst_2707_);
        return v___x_2710_;
    } else {
        let mut v___f_2712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2714_: *mut LeanObject,
    mut v_inst_2715_: *mut LeanObject,
    mut v_inst_2716_: *mut LeanObject,
    mut v_l_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    v___x_2718_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_HashSet_Raw_instEmptyCollection___closed__1_once),
        _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1,
    );
    v___x_2719_ = lean_uint8_once(
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once
        ),
        _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1,
    );
    if v___x_2719_ == 0 {
        lean_dec_ref(v_l_2717_);
        lean_dec_ref(v_inst_2716_);
        lean_dec_ref(v_inst_2715_);
        return v___x_2718_;
    } else {
        let mut v___f_2720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2722_);
    return v___x_2723_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(
    mut v_m_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2725_: *mut LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_2724_);
    lean_dec_ref(v_m_2724_);
    return v_res_2725_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets(
    mut v_00_u03b1_2726_: *mut LeanObject,
    mut v_m_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Std_HashSet_Raw_Internal_numBuckets___boxed(
    mut v_00_u03b1_2729_: *mut LeanObject,
    mut v_m_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2731_: *mut LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_2729_, v_m_2730_);
    lean_dec_ref(v_m_2730_);
    return v_res_2731_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg___lam__2(
    mut v_inst_2735_: *mut LeanObject,
    mut v___f_2736_: *mut LeanObject,
    mut v_m_2737_: *mut LeanObject,
    mut v_prec_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___f_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut v_unused_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = l_Std_HashSet_Raw_toList___redArg___closed__9;
                v_buckets_2740_ = lean_ctor_get(v_m_2737_, 1);
                v_isSharedCheck_2760_ = (!lean_is_exclusive(v_m_2737_)) as u8;
                if v_isSharedCheck_2760_ == 0 {
                    v_unused_2761_ = lean_ctor_get(v_m_2737_, 0);
                    lean_dec(v_unused_2761_);
                    v___x_2742_ = v_m_2737_;
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2740_);
                    lean_dec(v_m_2737_);
                    v___x_2742_ = lean_box(0);
                    v_isShared_2743_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2744_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1;
                v___x_2752_ = lean_box(0);
                v___x_2753_ = lean_array_get_size(v_buckets_2740_);
                v___x_2754_ = lean_unsigned_to_nat(0);
                v___x_2755_ = lean_nat_dec_lt(v___x_2754_, v___x_2753_);
                if v___x_2755_ == 0 {
                    lean_dec_ref(v_buckets_2740_);
                    lean_dec_ref(v___f_2736_);
                    v___y_2746_ = v___x_2752_;
                    state = 2;
                    continue;
                } else {
                    v___f_2756_ = lean_alloc_closure(
                        l_Std_HashSet_Raw_toList___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_2756_, 0, v___x_2739_);
                    lean_closure_set(v___f_2756_, 1, v___f_2736_);
                    v___x_2757_ = lean_usize_of_nat(v___x_2753_);
                    v___x_2758_ = 0usize;
                    v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                    lean_ctor_set_tag(v___x_2742_, 5);
                    lean_ctor_set(v___x_2742_, 1, v___x_2747_);
                    lean_ctor_set(v___x_2742_, 0, v___x_2744_);
                    v___x_2749_ = v___x_2742_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2744_);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2747_);
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
    mut v_inst_2762_: *mut LeanObject,
    mut v___f_2763_: *mut LeanObject,
    mut v_m_2764_: *mut LeanObject,
    mut v_prec_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2766_: *mut LeanObject = core::ptr::null_mut();
    v_res_2766_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(
        v_inst_2762_,
        v___f_2763_,
        v_m_2764_,
        v_prec_2765_,
    );
    lean_dec(v_prec_2765_);
    return v_res_2766_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr___redArg(
    mut v_inst_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2769_: *mut LeanObject = core::ptr::null_mut();
    v___f_2768_ = l_Std_HashSet_Raw_toList___redArg___closed__10;
    v___f_2769_ = lean_alloc_closure(
        l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2769_, 0, v_inst_2767_);
    lean_closure_set(v___f_2769_, 1, v___f_2768_);
    return v___f_2769_;
}
pub unsafe fn l_Std_HashSet_Raw_instRepr(
    mut v_00_u03b1_2770_: *mut LeanObject,
    mut v_inst_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_2771_);
    return v___x_2772_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Raw(builtin);
}
