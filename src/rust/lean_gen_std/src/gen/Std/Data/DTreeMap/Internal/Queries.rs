// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Queries
// Imports: Init.Data.Nat.Compare Std.Data.DTreeMap.Internal.Balanced Std.Data.DTreeMap.Internal.Ordered Init.BinderPredicates Init.Data.Option.BasicAux Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.Omega Init.RCases Init.WFTactics
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Nat::Compare::{
    initialize_Init_Data_Nat_Compare, runtime_initialize_Init_Data_Nat_Compare,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::r#gen::Std::Data::DTreeMap::Internal::Balanced::{
    initialize_Std_Data_DTreeMap_Internal_Balanced,
    runtime_initialize_Std_Data_DTreeMap_Internal_Balanced,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Ordered::{
    initialize_Std_Data_DTreeMap_Internal_Ordered,
    runtime_initialize_Std_Data_DTreeMap_Internal_Ordered,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub,
};
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
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
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [68, 84, 114, 101, 101, 77, 97, 112, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [73, 109, 112, 108, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
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
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        2223199789710442946 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        10691074554453191707 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_3:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        16557053633341250055 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        14749099308337200301 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
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
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_DTreeMap_Internal_Impl_term___x7em__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 113, 117, 105, 118, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,6049842283740396800 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value) as *mut crate::leanh::LeanObject,2223199789710442946 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value) as *mut crate::leanh::LeanObject,10691074554453191707 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value) as *mut crate::leanh::LeanObject,16557053633341250055 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value) as *mut crate::leanh::LeanObject,10522940562293801580 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110,
        116, 101, 114, 110, 97, 108, 46, 81, 117, 101, 114, 105, 101, 115, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 103, 101, 116, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        75, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32,
        105, 110, 32, 109, 97, 112, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 103, 101, 116, 69, 110, 116, 114, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 103, 101, 116, 75, 101, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 67, 111, 110, 115, 116, 46, 103, 101, 116, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value:
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
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 109, 105, 110, 69, 110, 116, 114, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [77, 97, 112, 32, 105, 115, 32, 101, 109, 112, 116, 121, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 109, 97, 120, 69, 110, 116, 114, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 109, 105, 110, 75, 101, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 109, 97, 120, 75, 101, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 101, 110, 116, 114, 121, 65, 116, 73, 100, 120, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1_value:
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
        79, 117, 116, 45, 111, 102, 45, 98, 111, 117, 110, 100, 115, 32, 97, 99, 99, 101, 115, 115,
        0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 107, 101, 121, 65, 116, 73, 100, 120, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 67, 111, 110, 115, 116, 46, 109, 105, 110, 69, 110, 116,
        114, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 67, 111, 110, 115, 116, 46, 109, 97, 120, 69, 110, 116,
        114, 121, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 73, 109, 112, 108, 46, 67, 111, 110, 115, 116, 46, 101, 110, 116, 114, 121, 65,
        116, 73, 100, 120, 33, 0,
    ],
};
static mut l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instCoeTypeForall(
    mut v_00_u03b1_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = crate::leanh::lean_box(0);
    return v___x_4294_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4338_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5;
    v___x_4339_ = l_String_toRawSubstring_x27(v___x_4338_);
    return v___x_4339_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(
    mut v_x_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    v___x_4365_ = l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5;
    crate::leanh::lean_inc(v_x_4362_);
    v___x_4366_ = l_Lean_Syntax_isOfKind(v_x_4362_, v___x_4365_);
    if v___x_4366_ == 0 {
        let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4362_);
        v___x_4367_ = crate::leanh::lean_box(1);
        v___x_4368_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4368_, 0, v___x_4367_);
        crate::leanh::lean_ctor_set(v___x_4368_, 1, v_a_4364_);
        return v___x_4368_;
    } else {
        let mut v_quotContext_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4376_: u8 = 0;
        let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4369_ = crate::leanh::lean_ctor_get(v_a_4363_, 1);
        v_currMacroScope_4370_ = crate::leanh::lean_ctor_get(v_a_4363_, 2);
        v_ref_4371_ = crate::leanh::lean_ctor_get(v_a_4363_, 5);
        v___x_4372_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4373_ = l_Lean_Syntax_getArg(v_x_4362_, v___x_4372_);
        v___x_4374_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4375_ = l_Lean_Syntax_getArg(v_x_4362_, v___x_4374_);
        crate::leanh::lean_dec(v_x_4362_);
        v___x_4376_ = 0;
        v___x_4377_ = l_Lean_SourceInfo_fromRef(v_ref_4371_, v___x_4376_);
        v___x_4378_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4;
        v___x_4379_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once), _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6);
        v___x_4380_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_4370_);
        crate::leanh::lean_inc(v_quotContext_4369_);
        v___x_4381_ =
            l_Lean_addMacroScope(v_quotContext_4369_, v___x_4380_, v_currMacroScope_4370_);
        v___x_4382_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12;
        crate::leanh::lean_inc_n(v___x_4377_, 2);
        v___x_4383_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4383_, 0, v___x_4377_);
        crate::leanh::lean_ctor_set(v___x_4383_, 1, v___x_4379_);
        crate::leanh::lean_ctor_set(v___x_4383_, 2, v___x_4381_);
        crate::leanh::lean_ctor_set(v___x_4383_, 3, v___x_4382_);
        v___x_4384_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14;
        v___x_4385_ = l_Lean_Syntax_node2(v___x_4377_, v___x_4384_, v___x_4373_, v___x_4375_);
        v___x_4386_ = l_Lean_Syntax_node2(v___x_4377_, v___x_4378_, v___x_4383_, v___x_4385_);
        v___x_4387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4386_);
        crate::leanh::lean_ctor_set(v___x_4387_, 1, v_a_4364_);
        return v___x_4387_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___boxed(
    mut v_x_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(v_x_4388_, v_a_4389_, v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    return v_res_4391_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(
    mut v_x_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    v___x_4398_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4;
    crate::leanh::lean_inc(v_x_4395_);
    v___x_4399_ = l_Lean_Syntax_isOfKind(v_x_4395_, v___x_4398_);
    if v___x_4399_ == 0 {
        let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4395_);
        v___x_4400_ = crate::leanh::lean_box(0);
        v___x_4401_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4401_, 0, v___x_4400_);
        crate::leanh::lean_ctor_set(v___x_4401_, 1, v_a_4397_);
        return v___x_4401_;
    } else {
        let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4405_: u8 = 0;
        v___x_4402_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4403_ = l_Lean_Syntax_getArg(v_x_4395_, v___x_4402_);
        v___x_4404_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1;
        crate::leanh::lean_inc(v___x_4403_);
        v___x_4405_ = l_Lean_Syntax_isOfKind(v___x_4403_, v___x_4404_);
        if v___x_4405_ == 0 {
            let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4403_);
            crate::leanh::lean_dec(v_x_4395_);
            v___x_4406_ = crate::leanh::lean_box(0);
            v___x_4407_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4407_, 0, v___x_4406_);
            crate::leanh::lean_ctor_set(v___x_4407_, 1, v_a_4397_);
            return v___x_4407_;
        } else {
            let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4411_: u8 = 0;
            v___x_4408_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4409_ = l_Lean_Syntax_getArg(v_x_4395_, v___x_4408_);
            crate::leanh::lean_dec(v_x_4395_);
            v___x_4410_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_4409_);
            v___x_4411_ = l_Lean_Syntax_matchesNull(v___x_4409_, v___x_4410_);
            if v___x_4411_ == 0 {
                let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4409_);
                crate::leanh::lean_dec(v___x_4403_);
                v___x_4412_ = crate::leanh::lean_box(0);
                v___x_4413_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4413_, 0, v___x_4412_);
                crate::leanh::lean_ctor_set(v___x_4413_, 1, v_a_4397_);
                return v___x_4413_;
            } else {
                let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4417_: u8 = 0;
                let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4414_ = l_Lean_Syntax_getArg(v___x_4409_, v___x_4402_);
                v___x_4415_ = l_Lean_Syntax_getArg(v___x_4409_, v___x_4408_);
                crate::leanh::lean_dec(v___x_4409_);
                v_ref_4416_ = l_Lean_replaceRef(v___x_4403_, v_a_4396_);
                crate::leanh::lean_dec(v___x_4403_);
                v___x_4417_ = 0;
                v___x_4418_ = l_Lean_SourceInfo_fromRef(v_ref_4416_, v___x_4417_);
                crate::leanh::lean_dec(v_ref_4416_);
                v___x_4419_ = l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5;
                v___x_4420_ = l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8;
                crate::leanh::lean_inc(v___x_4418_);
                v___x_4421_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4418_);
                crate::leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                v___x_4422_ = l_Lean_Syntax_node3(
                    v___x_4418_,
                    v___x_4419_,
                    v___x_4414_,
                    v___x_4421_,
                    v___x_4415_,
                );
                v___x_4423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4423_, 0, v___x_4422_);
                crate::leanh::lean_ctor_set(v___x_4423_, 1, v_a_4397_);
                return v___x_4423_;
            }
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(
    mut v_x_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4427_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(v_x_4424_, v_a_4425_, v_a_4426_);
    crate::leanh::lean_dec(v_a_4425_);
    return v_res_4427_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___redArg(
    mut v_inst_4428_: *mut crate::leanh::LeanObject,
    mut v_k_4429_: *mut crate::leanh::LeanObject,
    mut v_t_4430_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4437_: u8 = 0;
    let mut v___x_4439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4430_) == 0 {
                    v_k_4431_ = crate::leanh::lean_ctor_get(v_t_4430_, 1);
                    crate::leanh::lean_inc(v_k_4431_);
                    v_l_4432_ = crate::leanh::lean_ctor_get(v_t_4430_, 3);
                    crate::leanh::lean_inc(v_l_4432_);
                    v_r_4433_ = crate::leanh::lean_ctor_get(v_t_4430_, 4);
                    crate::leanh::lean_inc(v_r_4433_);
                    crate::leanh::lean_dec_ref_known(v_t_4430_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4428_);
                    crate::leanh::lean_inc(v_k_4429_);
                    v___x_4434_ = crate::leanh::lean_apply_2(v_inst_4428_, v_k_4429_, v_k_4431_);
                    v___x_4435_ = (crate::leanh::lean_unbox(v___x_4434_) as u8);
                    match v___x_4435_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4433_);
                            v_t_4430_ = v_l_4432_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4433_);
                            crate::leanh::lean_dec(v_l_4432_);
                            crate::leanh::lean_dec(v_k_4429_);
                            crate::leanh::lean_dec_ref(v_inst_4428_);
                            v___x_4437_ = 1;
                            return v___x_4437_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4432_);
                            v_t_4430_ = v_r_4433_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4429_);
                    crate::leanh::lean_dec_ref(v_inst_4428_);
                    v___x_4439_ = 0;
                    return v___x_4439_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(
    mut v_inst_4440_: *mut crate::leanh::LeanObject,
    mut v_k_4441_: *mut crate::leanh::LeanObject,
    mut v_t_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4443_: u8 = 0;
    let mut v_r_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4443_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_4440_, v_k_4441_, v_t_4442_);
    v_r_4444_ = crate::leanh::lean_box((v_res_4443_) as usize);
    return v_r_4444_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains(
    mut v_00_u03b1_4445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4446_: *mut crate::leanh::LeanObject,
    mut v_inst_4447_: *mut crate::leanh::LeanObject,
    mut v_k_4448_: *mut crate::leanh::LeanObject,
    mut v_t_4449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4450_: u8 = 0;
    v___x_4450_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_4447_, v_k_4448_, v_t_4449_);
    return v___x_4450_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___boxed(
    mut v_00_u03b1_4451_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4452_: *mut crate::leanh::LeanObject,
    mut v_inst_4453_: *mut crate::leanh::LeanObject,
    mut v_k_4454_: *mut crate::leanh::LeanObject,
    mut v_t_4455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4456_: u8 = 0;
    let mut v_r_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Std_DTreeMap_Internal_Impl_contains(
        v_00_u03b1_4451_,
        v_00_u03b2_4452_,
        v_inst_4453_,
        v_k_4454_,
        v_t_4455_,
    );
    v_r_4457_ = crate::leanh::lean_box((v_res_4456_) as usize);
    return v_r_4457_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(
    mut v_00_u03b1_4458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4459_: *mut crate::leanh::LeanObject,
    mut v_inst_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4461_ = crate::leanh::lean_box(0);
    return v___x_4461_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(
    mut v_00_u03b1_4462_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4463_: *mut crate::leanh::LeanObject,
    mut v_inst_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(
        v_00_u03b1_4462_,
        v_00_u03b2_4463_,
        v_inst_4464_,
    );
    crate::leanh::lean_dec_ref(v_inst_4464_);
    return v_res_4465_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(
    mut v_inst_4466_: *mut crate::leanh::LeanObject,
    mut v_m_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4469_: u8 = 0;
    v___x_4469_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_4466_, v_a_4468_, v_m_4467_);
    return v___x_4469_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(
    mut v_inst_4470_: *mut crate::leanh::LeanObject,
    mut v_m_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4473_: u8 = 0;
    let mut v_r_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4473_ =
        l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_4470_, v_m_4471_, v_a_4472_);
    v_r_4474_ = crate::leanh::lean_box((v_res_4473_) as usize);
    return v_r_4474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instDecidableMem(
    mut v_00_u03b1_4475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4476_: *mut crate::leanh::LeanObject,
    mut v_inst_4477_: *mut crate::leanh::LeanObject,
    mut v_m_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4480_: u8 = 0;
    v___x_4480_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_4477_, v_a_4479_, v_m_4478_);
    return v___x_4480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(
    mut v_00_u03b1_4481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4482_: *mut crate::leanh::LeanObject,
    mut v_inst_4483_: *mut crate::leanh::LeanObject,
    mut v_m_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4486_: u8 = 0;
    let mut v_r_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4486_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(
        v_00_u03b1_4481_,
        v_00_u03b2_4482_,
        v_inst_4483_,
        v_m_4484_,
        v_a_4485_,
    );
    v_r_4487_ = crate::leanh::lean_box((v_res_4486_) as usize);
    return v_r_4487_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(
    mut v_t_4488_: *mut crate::leanh::LeanObject,
    mut v_h__1_4489_: *mut crate::leanh::LeanObject,
    mut v_h__2_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4488_) == 0 {
        let mut v_size_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4489_);
        v_size_4491_ = crate::leanh::lean_ctor_get(v_t_4488_, 0);
        crate::leanh::lean_inc(v_size_4491_);
        v_k_4492_ = crate::leanh::lean_ctor_get(v_t_4488_, 1);
        crate::leanh::lean_inc(v_k_4492_);
        v_v_4493_ = crate::leanh::lean_ctor_get(v_t_4488_, 2);
        crate::leanh::lean_inc(v_v_4493_);
        v_l_4494_ = crate::leanh::lean_ctor_get(v_t_4488_, 3);
        crate::leanh::lean_inc(v_l_4494_);
        v_r_4495_ = crate::leanh::lean_ctor_get(v_t_4488_, 4);
        crate::leanh::lean_inc(v_r_4495_);
        crate::leanh::lean_dec_ref_known(v_t_4488_, 5);
        v___x_4496_ = crate::leanh::lean_apply_5(
            v_h__2_4490_,
            v_size_4491_,
            v_k_4492_,
            v_v_4493_,
            v_l_4494_,
            v_r_4495_,
        );
        return v___x_4496_;
    } else {
        let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4490_);
        v___x_4497_ = crate::leanh::lean_box(0);
        v___x_4498_ = crate::leanh::lean_apply_1(v_h__1_4489_, v___x_4497_);
        return v___x_4498_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(
    mut v_00_u03b1_4499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4500_: *mut crate::leanh::LeanObject,
    mut v_motive_4501_: *mut crate::leanh::LeanObject,
    mut v_t_4502_: *mut crate::leanh::LeanObject,
    mut v_h__1_4503_: *mut crate::leanh::LeanObject,
    mut v_h__2_4504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4502_) == 0 {
        let mut v_size_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4503_);
        v_size_4505_ = crate::leanh::lean_ctor_get(v_t_4502_, 0);
        crate::leanh::lean_inc(v_size_4505_);
        v_k_4506_ = crate::leanh::lean_ctor_get(v_t_4502_, 1);
        crate::leanh::lean_inc(v_k_4506_);
        v_v_4507_ = crate::leanh::lean_ctor_get(v_t_4502_, 2);
        crate::leanh::lean_inc(v_v_4507_);
        v_l_4508_ = crate::leanh::lean_ctor_get(v_t_4502_, 3);
        crate::leanh::lean_inc(v_l_4508_);
        v_r_4509_ = crate::leanh::lean_ctor_get(v_t_4502_, 4);
        crate::leanh::lean_inc(v_r_4509_);
        crate::leanh::lean_dec_ref_known(v_t_4502_, 5);
        v___x_4510_ = crate::leanh::lean_apply_5(
            v_h__2_4504_,
            v_size_4505_,
            v_k_4506_,
            v_v_4507_,
            v_l_4508_,
            v_r_4509_,
        );
        return v___x_4510_;
    } else {
        let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4504_);
        v___x_4511_ = crate::leanh::lean_box(0);
        v___x_4512_ = crate::leanh::lean_apply_1(v_h__1_4503_, v___x_4511_);
        return v___x_4512_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(
    mut v_x_4513_: u8,
    mut v_h__1_4514_: *mut crate::leanh::LeanObject,
    mut v_h__2_4515_: *mut crate::leanh::LeanObject,
    mut v_h__3_4516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_4513_ {
        0 => {
            let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4516_);
            crate::leanh::lean_dec(v_h__2_4515_);
            v___x_4517_ = crate::leanh::lean_box(0);
            v___x_4518_ = crate::leanh::lean_apply_1(v_h__1_4514_, v___x_4517_);
            return v___x_4518_;
        }
        1 => {
            let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4515_);
            crate::leanh::lean_dec(v_h__1_4514_);
            v___x_4519_ = crate::leanh::lean_box(0);
            v___x_4520_ = crate::leanh::lean_apply_1(v_h__3_4516_, v___x_4519_);
            return v___x_4520_;
        }
        _ => {
            let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4516_);
            crate::leanh::lean_dec(v_h__1_4514_);
            v___x_4521_ = crate::leanh::lean_box(0);
            v___x_4522_ = crate::leanh::lean_apply_1(v_h__2_4515_, v___x_4521_);
            return v___x_4522_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(
    mut v_x_4523_: *mut crate::leanh::LeanObject,
    mut v_h__1_4524_: *mut crate::leanh::LeanObject,
    mut v_h__2_4525_: *mut crate::leanh::LeanObject,
    mut v_h__3_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_4527_: u8 = 0;
    let mut v_res_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4527_ = (crate::leanh::lean_unbox(v_x_4523_) as u8);
    v_res_4528_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_4527_, v_h__1_4524_, v_h__2_4525_, v_h__3_4526_);
    return v_res_4528_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(
    mut v_motive_4529_: *mut crate::leanh::LeanObject,
    mut v_x_4530_: u8,
    mut v_h__1_4531_: *mut crate::leanh::LeanObject,
    mut v_h__2_4532_: *mut crate::leanh::LeanObject,
    mut v_h__3_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_4530_ {
        0 => {
            let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4533_);
            crate::leanh::lean_dec(v_h__2_4532_);
            v___x_4534_ = crate::leanh::lean_box(0);
            v___x_4535_ = crate::leanh::lean_apply_1(v_h__1_4531_, v___x_4534_);
            return v___x_4535_;
        }
        1 => {
            let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4532_);
            crate::leanh::lean_dec(v_h__1_4531_);
            v___x_4536_ = crate::leanh::lean_box(0);
            v___x_4537_ = crate::leanh::lean_apply_1(v_h__3_4533_, v___x_4536_);
            return v___x_4537_;
        }
        _ => {
            let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4533_);
            crate::leanh::lean_dec(v_h__1_4531_);
            v___x_4538_ = crate::leanh::lean_box(0);
            v___x_4539_ = crate::leanh::lean_apply_1(v_h__2_4532_, v___x_4538_);
            return v___x_4539_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(
    mut v_motive_4540_: *mut crate::leanh::LeanObject,
    mut v_x_4541_: *mut crate::leanh::LeanObject,
    mut v_h__1_4542_: *mut crate::leanh::LeanObject,
    mut v_h__2_4543_: *mut crate::leanh::LeanObject,
    mut v_h__3_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_4545_: u8 = 0;
    let mut v_res_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_4545_ = (crate::leanh::lean_unbox(v_x_4541_) as u8);
    v_res_4546_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_4540_, v_x_51__boxed_4545_, v_h__1_4542_, v_h__2_4543_, v_h__3_4544_);
    return v_res_4546_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(
    mut v_t_4547_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_4547_) == 0 {
        let mut v___x_4548_: u8 = 0;
        v___x_4548_ = 0;
        return v___x_4548_;
    } else {
        let mut v___x_4549_: u8 = 0;
        v___x_4549_ = 1;
        return v___x_4549_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(
    mut v_t_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4551_: u8 = 0;
    let mut v_r_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_4550_);
    crate::leanh::lean_dec(v_t_4550_);
    v_r_4552_ = crate::leanh::lean_box((v_res_4551_) as usize);
    return v_r_4552_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_isEmpty(
    mut v_00_u03b1_4553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4554_: *mut crate::leanh::LeanObject,
    mut v_t_4555_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_t_4555_) == 0 {
        let mut v___x_4556_: u8 = 0;
        v___x_4556_ = 0;
        return v___x_4556_;
    } else {
        let mut v___x_4557_: u8 = 0;
        v___x_4557_ = 1;
        return v___x_4557_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(
    mut v_00_u03b1_4558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4559_: *mut crate::leanh::LeanObject,
    mut v_t_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4561_: u8 = 0;
    let mut v_r_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ =
        l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_4558_, v_00_u03b2_4559_, v_t_4560_);
    crate::leanh::lean_dec(v_t_4560_);
    v_r_4562_ = crate::leanh::lean_box((v_res_4561_) as usize);
    return v_r_4562_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
    mut v_inst_4563_: *mut crate::leanh::LeanObject,
    mut v_t_4564_: *mut crate::leanh::LeanObject,
    mut v_k_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4564_) == 0 {
                    v_k_4566_ = crate::leanh::lean_ctor_get(v_t_4564_, 1);
                    crate::leanh::lean_inc(v_k_4566_);
                    v_v_4567_ = crate::leanh::lean_ctor_get(v_t_4564_, 2);
                    crate::leanh::lean_inc(v_v_4567_);
                    v_l_4568_ = crate::leanh::lean_ctor_get(v_t_4564_, 3);
                    crate::leanh::lean_inc(v_l_4568_);
                    v_r_4569_ = crate::leanh::lean_ctor_get(v_t_4564_, 4);
                    crate::leanh::lean_inc(v_r_4569_);
                    crate::leanh::lean_dec_ref_known(v_t_4564_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4563_);
                    crate::leanh::lean_inc(v_k_4565_);
                    v___x_4570_ = crate::leanh::lean_apply_2(v_inst_4563_, v_k_4565_, v_k_4566_);
                    v___x_4571_ = (crate::leanh::lean_unbox(v___x_4570_) as u8);
                    match v___x_4571_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4569_);
                            crate::leanh::lean_dec(v_v_4567_);
                            v_t_4564_ = v_l_4568_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4569_);
                            crate::leanh::lean_dec(v_l_4568_);
                            crate::leanh::lean_dec(v_k_4565_);
                            crate::leanh::lean_dec_ref(v_inst_4563_);
                            v___x_4573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4573_, 0, v_v_4567_);
                            return v___x_4573_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4568_);
                            crate::leanh::lean_dec(v_v_4567_);
                            v_t_4564_ = v_r_4569_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4565_);
                    crate::leanh::lean_dec_ref(v_inst_4563_);
                    v___x_4575_ = crate::leanh::lean_box(0);
                    return v___x_4575_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f(
    mut v_00_u03b1_4576_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4577_: *mut crate::leanh::LeanObject,
    mut v_inst_4578_: *mut crate::leanh::LeanObject,
    mut v_inst_4579_: *mut crate::leanh::LeanObject,
    mut v_t_4580_: *mut crate::leanh::LeanObject,
    mut v_k_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_4578_, v_t_4580_, v_k_4581_);
    return v___x_4582_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get___redArg(
    mut v_inst_4583_: *mut crate::leanh::LeanObject,
    mut v_t_4584_: *mut crate::leanh::LeanObject,
    mut v_k_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4586_ = crate::leanh::lean_ctor_get(v_t_4584_, 1);
                crate::leanh::lean_inc(v_k_4586_);
                v_v_4587_ = crate::leanh::lean_ctor_get(v_t_4584_, 2);
                crate::leanh::lean_inc(v_v_4587_);
                v_l_4588_ = crate::leanh::lean_ctor_get(v_t_4584_, 3);
                crate::leanh::lean_inc(v_l_4588_);
                v_r_4589_ = crate::leanh::lean_ctor_get(v_t_4584_, 4);
                crate::leanh::lean_inc(v_r_4589_);
                crate::leanh::lean_dec(v_t_4584_);
                crate::leanh::lean_inc_ref(v_inst_4583_);
                crate::leanh::lean_inc(v_k_4585_);
                v___x_4590_ = crate::leanh::lean_apply_2(v_inst_4583_, v_k_4585_, v_k_4586_);
                v___x_4591_ = (crate::leanh::lean_unbox(v___x_4590_) as u8);
                match v___x_4591_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_4589_);
                        crate::leanh::lean_dec(v_v_4587_);
                        v_t_4584_ = v_l_4588_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_4589_);
                        crate::leanh::lean_dec(v_l_4588_);
                        crate::leanh::lean_dec(v_k_4585_);
                        crate::leanh::lean_dec_ref(v_inst_4583_);
                        return v_v_4587_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_4588_);
                        crate::leanh::lean_dec(v_v_4587_);
                        v_t_4584_ = v_r_4589_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get(
    mut v_00_u03b1_4594_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4595_: *mut crate::leanh::LeanObject,
    mut v_inst_4596_: *mut crate::leanh::LeanObject,
    mut v_inst_4597_: *mut crate::leanh::LeanObject,
    mut v_t_4598_: *mut crate::leanh::LeanObject,
    mut v_k_4599_: *mut crate::leanh::LeanObject,
    mut v_hlk_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_4596_, v_t_4598_, v_k_4599_);
    return v___x_4601_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4605_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2;
    v___x_4606_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_4607_ = crate::leanh::lean_unsigned_to_nat(108);
    v___x_4608_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1;
    v___x_4609_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_4610_ = l_mkPanicMessageWithDecl(
        v___x_4609_,
        v___x_4608_,
        v___x_4607_,
        v___x_4606_,
        v___x_4605_,
    );
    return v___x_4610_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
    mut v_inst_4611_: *mut crate::leanh::LeanObject,
    mut v_t_4612_: *mut crate::leanh::LeanObject,
    mut v_k_4613_: *mut crate::leanh::LeanObject,
    mut v_inst_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4612_) == 0 {
                    v_k_4615_ = crate::leanh::lean_ctor_get(v_t_4612_, 1);
                    crate::leanh::lean_inc(v_k_4615_);
                    v_v_4616_ = crate::leanh::lean_ctor_get(v_t_4612_, 2);
                    crate::leanh::lean_inc(v_v_4616_);
                    v_l_4617_ = crate::leanh::lean_ctor_get(v_t_4612_, 3);
                    crate::leanh::lean_inc(v_l_4617_);
                    v_r_4618_ = crate::leanh::lean_ctor_get(v_t_4612_, 4);
                    crate::leanh::lean_inc(v_r_4618_);
                    crate::leanh::lean_dec_ref_known(v_t_4612_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4611_);
                    crate::leanh::lean_inc(v_k_4613_);
                    v___x_4619_ = crate::leanh::lean_apply_2(v_inst_4611_, v_k_4613_, v_k_4615_);
                    v___x_4620_ = (crate::leanh::lean_unbox(v___x_4619_) as u8);
                    match v___x_4620_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4618_);
                            crate::leanh::lean_dec(v_v_4616_);
                            v_t_4612_ = v_l_4617_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4618_);
                            crate::leanh::lean_dec(v_l_4617_);
                            crate::leanh::lean_dec(v_k_4613_);
                            crate::leanh::lean_dec_ref(v_inst_4611_);
                            return v_v_4616_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4617_);
                            crate::leanh::lean_dec(v_v_4616_);
                            v_t_4612_ = v_r_4618_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4613_);
                    crate::leanh::lean_dec_ref(v_inst_4611_);
                    v___x_4623_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3,
                    );
                    v___x_4624_ = l_panic___redArg(v_inst_4614_, v___x_4623_);
                    return v___x_4624_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(
    mut v_inst_4625_: *mut crate::leanh::LeanObject,
    mut v_t_4626_: *mut crate::leanh::LeanObject,
    mut v_k_4627_: *mut crate::leanh::LeanObject,
    mut v_inst_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4629_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_inst_4625_,
        v_t_4626_,
        v_k_4627_,
        v_inst_4628_,
    );
    crate::leanh::lean_dec(v_inst_4628_);
    return v_res_4629_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21(
    mut v_00_u03b1_4630_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4631_: *mut crate::leanh::LeanObject,
    mut v_inst_4632_: *mut crate::leanh::LeanObject,
    mut v_inst_4633_: *mut crate::leanh::LeanObject,
    mut v_t_4634_: *mut crate::leanh::LeanObject,
    mut v_k_4635_: *mut crate::leanh::LeanObject,
    mut v_inst_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(
        v_inst_4632_,
        v_t_4634_,
        v_k_4635_,
        v_inst_4636_,
    );
    return v___x_4637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x21___boxed(
    mut v_00_u03b1_4638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4639_: *mut crate::leanh::LeanObject,
    mut v_inst_4640_: *mut crate::leanh::LeanObject,
    mut v_inst_4641_: *mut crate::leanh::LeanObject,
    mut v_t_4642_: *mut crate::leanh::LeanObject,
    mut v_k_4643_: *mut crate::leanh::LeanObject,
    mut v_inst_4644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4645_ = l_Std_DTreeMap_Internal_Impl_get_x21(
        v_00_u03b1_4638_,
        v_00_u03b2_4639_,
        v_inst_4640_,
        v_inst_4641_,
        v_t_4642_,
        v_k_4643_,
        v_inst_4644_,
    );
    crate::leanh::lean_dec(v_inst_4644_);
    return v_res_4645_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD___redArg(
    mut v_inst_4646_: *mut crate::leanh::LeanObject,
    mut v_t_4647_: *mut crate::leanh::LeanObject,
    mut v_k_4648_: *mut crate::leanh::LeanObject,
    mut v_fallback_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4647_) == 0 {
                    v_k_4650_ = crate::leanh::lean_ctor_get(v_t_4647_, 1);
                    crate::leanh::lean_inc(v_k_4650_);
                    v_v_4651_ = crate::leanh::lean_ctor_get(v_t_4647_, 2);
                    crate::leanh::lean_inc(v_v_4651_);
                    v_l_4652_ = crate::leanh::lean_ctor_get(v_t_4647_, 3);
                    crate::leanh::lean_inc(v_l_4652_);
                    v_r_4653_ = crate::leanh::lean_ctor_get(v_t_4647_, 4);
                    crate::leanh::lean_inc(v_r_4653_);
                    crate::leanh::lean_dec_ref_known(v_t_4647_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4646_);
                    crate::leanh::lean_inc(v_k_4648_);
                    v___x_4654_ = crate::leanh::lean_apply_2(v_inst_4646_, v_k_4648_, v_k_4650_);
                    v___x_4655_ = (crate::leanh::lean_unbox(v___x_4654_) as u8);
                    match v___x_4655_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4653_);
                            crate::leanh::lean_dec(v_v_4651_);
                            v_t_4647_ = v_l_4652_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4653_);
                            crate::leanh::lean_dec(v_l_4652_);
                            crate::leanh::lean_dec(v_k_4648_);
                            crate::leanh::lean_dec_ref(v_inst_4646_);
                            return v_v_4651_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4652_);
                            crate::leanh::lean_dec(v_v_4651_);
                            v_t_4647_ = v_r_4653_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4648_);
                    crate::leanh::lean_dec_ref(v_inst_4646_);
                    crate::leanh::lean_inc(v_fallback_4649_);
                    return v_fallback_4649_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(
    mut v_inst_4658_: *mut crate::leanh::LeanObject,
    mut v_t_4659_: *mut crate::leanh::LeanObject,
    mut v_k_4660_: *mut crate::leanh::LeanObject,
    mut v_fallback_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_inst_4658_,
        v_t_4659_,
        v_k_4660_,
        v_fallback_4661_,
    );
    crate::leanh::lean_dec(v_fallback_4661_);
    return v_res_4662_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD(
    mut v_00_u03b1_4663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4664_: *mut crate::leanh::LeanObject,
    mut v_inst_4665_: *mut crate::leanh::LeanObject,
    mut v_inst_4666_: *mut crate::leanh::LeanObject,
    mut v_t_4667_: *mut crate::leanh::LeanObject,
    mut v_k_4668_: *mut crate::leanh::LeanObject,
    mut v_fallback_4669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4670_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(
        v_inst_4665_,
        v_t_4667_,
        v_k_4668_,
        v_fallback_4669_,
    );
    return v___x_4670_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getD___boxed(
    mut v_00_u03b1_4671_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4672_: *mut crate::leanh::LeanObject,
    mut v_inst_4673_: *mut crate::leanh::LeanObject,
    mut v_inst_4674_: *mut crate::leanh::LeanObject,
    mut v_t_4675_: *mut crate::leanh::LeanObject,
    mut v_k_4676_: *mut crate::leanh::LeanObject,
    mut v_fallback_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4678_ = l_Std_DTreeMap_Internal_Impl_getD(
        v_00_u03b1_4671_,
        v_00_u03b2_4672_,
        v_inst_4673_,
        v_inst_4674_,
        v_t_4675_,
        v_k_4676_,
        v_fallback_4677_,
    );
    crate::leanh::lean_dec(v_fallback_4677_);
    return v_res_4678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(
    mut v_inst_4679_: *mut crate::leanh::LeanObject,
    mut v_t_4680_: *mut crate::leanh::LeanObject,
    mut v_k_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4680_) == 0 {
                    v_k_4682_ = crate::leanh::lean_ctor_get(v_t_4680_, 1);
                    crate::leanh::lean_inc_n(v_k_4682_, 2);
                    v_v_4683_ = crate::leanh::lean_ctor_get(v_t_4680_, 2);
                    crate::leanh::lean_inc(v_v_4683_);
                    v_l_4684_ = crate::leanh::lean_ctor_get(v_t_4680_, 3);
                    crate::leanh::lean_inc(v_l_4684_);
                    v_r_4685_ = crate::leanh::lean_ctor_get(v_t_4680_, 4);
                    crate::leanh::lean_inc(v_r_4685_);
                    crate::leanh::lean_dec_ref_known(v_t_4680_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4679_);
                    crate::leanh::lean_inc(v_k_4681_);
                    v___x_4686_ = crate::leanh::lean_apply_2(v_inst_4679_, v_k_4681_, v_k_4682_);
                    v___x_4687_ = (crate::leanh::lean_unbox(v___x_4686_) as u8);
                    match v___x_4687_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4685_);
                            crate::leanh::lean_dec(v_v_4683_);
                            crate::leanh::lean_dec(v_k_4682_);
                            v_t_4680_ = v_l_4684_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4685_);
                            crate::leanh::lean_dec(v_l_4684_);
                            crate::leanh::lean_dec(v_k_4681_);
                            crate::leanh::lean_dec_ref(v_inst_4679_);
                            v___x_4689_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4689_, 0, v_k_4682_);
                            crate::leanh::lean_ctor_set(v___x_4689_, 1, v_v_4683_);
                            v___x_4690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
                            return v___x_4690_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4684_);
                            crate::leanh::lean_dec(v_v_4683_);
                            crate::leanh::lean_dec(v_k_4682_);
                            v_t_4680_ = v_r_4685_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4681_);
                    crate::leanh::lean_dec_ref(v_inst_4679_);
                    v___x_4692_ = crate::leanh::lean_box(0);
                    return v___x_4692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x3f(
    mut v_00_u03b1_4693_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4694_: *mut crate::leanh::LeanObject,
    mut v_inst_4695_: *mut crate::leanh::LeanObject,
    mut v_t_4696_: *mut crate::leanh::LeanObject,
    mut v_k_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ =
        l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_4695_, v_t_4696_, v_k_4697_);
    return v___x_4698_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry___redArg(
    mut v_inst_4699_: *mut crate::leanh::LeanObject,
    mut v_t_4700_: *mut crate::leanh::LeanObject,
    mut v_k_4701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: u8 = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4702_ = crate::leanh::lean_ctor_get(v_t_4700_, 1);
                crate::leanh::lean_inc_n(v_k_4702_, 2);
                v_v_4703_ = crate::leanh::lean_ctor_get(v_t_4700_, 2);
                crate::leanh::lean_inc(v_v_4703_);
                v_l_4704_ = crate::leanh::lean_ctor_get(v_t_4700_, 3);
                crate::leanh::lean_inc(v_l_4704_);
                v_r_4705_ = crate::leanh::lean_ctor_get(v_t_4700_, 4);
                crate::leanh::lean_inc(v_r_4705_);
                crate::leanh::lean_dec(v_t_4700_);
                crate::leanh::lean_inc_ref(v_inst_4699_);
                crate::leanh::lean_inc(v_k_4701_);
                v___x_4706_ = crate::leanh::lean_apply_2(v_inst_4699_, v_k_4701_, v_k_4702_);
                v___x_4707_ = (crate::leanh::lean_unbox(v___x_4706_) as u8);
                match v___x_4707_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_4705_);
                        crate::leanh::lean_dec(v_v_4703_);
                        crate::leanh::lean_dec(v_k_4702_);
                        v_t_4700_ = v_l_4704_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_4705_);
                        crate::leanh::lean_dec(v_l_4704_);
                        crate::leanh::lean_dec(v_k_4701_);
                        crate::leanh::lean_dec_ref(v_inst_4699_);
                        v___x_4709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4709_, 0, v_k_4702_);
                        crate::leanh::lean_ctor_set(v___x_4709_, 1, v_v_4703_);
                        return v___x_4709_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_4704_);
                        crate::leanh::lean_dec(v_v_4703_);
                        crate::leanh::lean_dec(v_k_4702_);
                        v_t_4700_ = v_r_4705_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry(
    mut v_00_u03b1_4711_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4712_: *mut crate::leanh::LeanObject,
    mut v_inst_4713_: *mut crate::leanh::LeanObject,
    mut v_t_4714_: *mut crate::leanh::LeanObject,
    mut v_k_4715_: *mut crate::leanh::LeanObject,
    mut v_hlk_4716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ =
        l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_4713_, v_t_4714_, v_k_4715_);
    return v___x_4717_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4719_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2;
    v___x_4720_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_4721_ = crate::leanh::lean_unsigned_to_nat(147);
    v___x_4722_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0;
    v___x_4723_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_4724_ = l_mkPanicMessageWithDecl(
        v___x_4723_,
        v___x_4722_,
        v___x_4721_,
        v___x_4720_,
        v___x_4719_,
    );
    return v___x_4724_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(
    mut v_inst_4725_: *mut crate::leanh::LeanObject,
    mut v_inst_4726_: *mut crate::leanh::LeanObject,
    mut v_t_4727_: *mut crate::leanh::LeanObject,
    mut v_k_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: u8 = 0;
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4727_) == 0 {
                    v_k_4729_ = crate::leanh::lean_ctor_get(v_t_4727_, 1);
                    crate::leanh::lean_inc_n(v_k_4729_, 2);
                    v_v_4730_ = crate::leanh::lean_ctor_get(v_t_4727_, 2);
                    crate::leanh::lean_inc(v_v_4730_);
                    v_l_4731_ = crate::leanh::lean_ctor_get(v_t_4727_, 3);
                    crate::leanh::lean_inc(v_l_4731_);
                    v_r_4732_ = crate::leanh::lean_ctor_get(v_t_4727_, 4);
                    crate::leanh::lean_inc(v_r_4732_);
                    crate::leanh::lean_dec_ref_known(v_t_4727_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4725_);
                    crate::leanh::lean_inc(v_k_4728_);
                    v___x_4733_ = crate::leanh::lean_apply_2(v_inst_4725_, v_k_4728_, v_k_4729_);
                    v___x_4734_ = (crate::leanh::lean_unbox(v___x_4733_) as u8);
                    match v___x_4734_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4732_);
                            crate::leanh::lean_dec(v_v_4730_);
                            crate::leanh::lean_dec(v_k_4729_);
                            v_t_4727_ = v_l_4731_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4732_);
                            crate::leanh::lean_dec(v_l_4731_);
                            crate::leanh::lean_dec(v_k_4728_);
                            crate::leanh::lean_dec_ref(v_inst_4725_);
                            v___x_4736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4736_, 0, v_k_4729_);
                            crate::leanh::lean_ctor_set(v___x_4736_, 1, v_v_4730_);
                            return v___x_4736_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4731_);
                            crate::leanh::lean_dec(v_v_4730_);
                            crate::leanh::lean_dec(v_k_4729_);
                            v_t_4727_ = v_r_4732_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4728_);
                    crate::leanh::lean_dec_ref(v_inst_4725_);
                    v___x_4738_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1,
                    );
                    v___x_4739_ = l_panic___redArg(v_inst_4726_, v___x_4738_);
                    return v___x_4739_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(
    mut v_inst_4740_: *mut crate::leanh::LeanObject,
    mut v_inst_4741_: *mut crate::leanh::LeanObject,
    mut v_t_4742_: *mut crate::leanh::LeanObject,
    mut v_k_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4744_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(
        v_inst_4740_,
        v_inst_4741_,
        v_t_4742_,
        v_k_4743_,
    );
    crate::leanh::lean_dec_ref(v_inst_4741_);
    return v_res_4744_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21(
    mut v_00_u03b1_4745_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4746_: *mut crate::leanh::LeanObject,
    mut v_inst_4747_: *mut crate::leanh::LeanObject,
    mut v_inst_4748_: *mut crate::leanh::LeanObject,
    mut v_t_4749_: *mut crate::leanh::LeanObject,
    mut v_k_4750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4751_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(
        v_inst_4747_,
        v_inst_4748_,
        v_t_4749_,
        v_k_4750_,
    );
    return v___x_4751_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(
    mut v_00_u03b1_4752_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4753_: *mut crate::leanh::LeanObject,
    mut v_inst_4754_: *mut crate::leanh::LeanObject,
    mut v_inst_4755_: *mut crate::leanh::LeanObject,
    mut v_t_4756_: *mut crate::leanh::LeanObject,
    mut v_k_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21(
        v_00_u03b1_4752_,
        v_00_u03b2_4753_,
        v_inst_4754_,
        v_inst_4755_,
        v_t_4756_,
        v_k_4757_,
    );
    crate::leanh::lean_dec_ref(v_inst_4755_);
    return v_res_4758_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(
    mut v_inst_4759_: *mut crate::leanh::LeanObject,
    mut v_t_4760_: *mut crate::leanh::LeanObject,
    mut v_k_4761_: *mut crate::leanh::LeanObject,
    mut v_fallback_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4760_) == 0 {
                    v_k_4763_ = crate::leanh::lean_ctor_get(v_t_4760_, 1);
                    crate::leanh::lean_inc_n(v_k_4763_, 2);
                    v_v_4764_ = crate::leanh::lean_ctor_get(v_t_4760_, 2);
                    crate::leanh::lean_inc(v_v_4764_);
                    v_l_4765_ = crate::leanh::lean_ctor_get(v_t_4760_, 3);
                    crate::leanh::lean_inc(v_l_4765_);
                    v_r_4766_ = crate::leanh::lean_ctor_get(v_t_4760_, 4);
                    crate::leanh::lean_inc(v_r_4766_);
                    crate::leanh::lean_dec_ref_known(v_t_4760_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4759_);
                    crate::leanh::lean_inc(v_k_4761_);
                    v___x_4767_ = crate::leanh::lean_apply_2(v_inst_4759_, v_k_4761_, v_k_4763_);
                    v___x_4768_ = (crate::leanh::lean_unbox(v___x_4767_) as u8);
                    match v___x_4768_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4766_);
                            crate::leanh::lean_dec(v_v_4764_);
                            crate::leanh::lean_dec(v_k_4763_);
                            v_t_4760_ = v_l_4765_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4766_);
                            crate::leanh::lean_dec(v_l_4765_);
                            crate::leanh::lean_dec(v_k_4761_);
                            crate::leanh::lean_dec_ref(v_inst_4759_);
                            v___x_4770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4770_, 0, v_k_4763_);
                            crate::leanh::lean_ctor_set(v___x_4770_, 1, v_v_4764_);
                            return v___x_4770_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4765_);
                            crate::leanh::lean_dec(v_v_4764_);
                            crate::leanh::lean_dec(v_k_4763_);
                            v_t_4760_ = v_r_4766_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4761_);
                    crate::leanh::lean_dec_ref(v_inst_4759_);
                    crate::leanh::lean_inc_ref(v_fallback_4762_);
                    return v_fallback_4762_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(
    mut v_inst_4772_: *mut crate::leanh::LeanObject,
    mut v_t_4773_: *mut crate::leanh::LeanObject,
    mut v_k_4774_: *mut crate::leanh::LeanObject,
    mut v_fallback_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4776_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(
        v_inst_4772_,
        v_t_4773_,
        v_k_4774_,
        v_fallback_4775_,
    );
    crate::leanh::lean_dec_ref(v_fallback_4775_);
    return v_res_4776_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD(
    mut v_00_u03b1_4777_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4778_: *mut crate::leanh::LeanObject,
    mut v_inst_4779_: *mut crate::leanh::LeanObject,
    mut v_t_4780_: *mut crate::leanh::LeanObject,
    mut v_k_4781_: *mut crate::leanh::LeanObject,
    mut v_fallback_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4783_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(
        v_inst_4779_,
        v_t_4780_,
        v_k_4781_,
        v_fallback_4782_,
    );
    return v___x_4783_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(
    mut v_00_u03b1_4784_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4785_: *mut crate::leanh::LeanObject,
    mut v_inst_4786_: *mut crate::leanh::LeanObject,
    mut v_t_4787_: *mut crate::leanh::LeanObject,
    mut v_k_4788_: *mut crate::leanh::LeanObject,
    mut v_fallback_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Std_DTreeMap_Internal_Impl_getEntryD(
        v_00_u03b1_4784_,
        v_00_u03b2_4785_,
        v_inst_4786_,
        v_t_4787_,
        v_k_4788_,
        v_fallback_4789_,
    );
    crate::leanh::lean_dec_ref(v_fallback_4789_);
    return v_res_4790_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(
    mut v_inst_4791_: *mut crate::leanh::LeanObject,
    mut v_t_4792_: *mut crate::leanh::LeanObject,
    mut v_k_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: u8 = 0;
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4792_) == 0 {
                    v_k_4794_ = crate::leanh::lean_ctor_get(v_t_4792_, 1);
                    crate::leanh::lean_inc_n(v_k_4794_, 2);
                    v_l_4795_ = crate::leanh::lean_ctor_get(v_t_4792_, 3);
                    crate::leanh::lean_inc(v_l_4795_);
                    v_r_4796_ = crate::leanh::lean_ctor_get(v_t_4792_, 4);
                    crate::leanh::lean_inc(v_r_4796_);
                    crate::leanh::lean_dec_ref_known(v_t_4792_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4791_);
                    crate::leanh::lean_inc(v_k_4793_);
                    v___x_4797_ = crate::leanh::lean_apply_2(v_inst_4791_, v_k_4793_, v_k_4794_);
                    v___x_4798_ = (crate::leanh::lean_unbox(v___x_4797_) as u8);
                    match v___x_4798_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4796_);
                            crate::leanh::lean_dec(v_k_4794_);
                            v_t_4792_ = v_l_4795_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4796_);
                            crate::leanh::lean_dec(v_l_4795_);
                            crate::leanh::lean_dec(v_k_4793_);
                            crate::leanh::lean_dec_ref(v_inst_4791_);
                            v___x_4800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4800_, 0, v_k_4794_);
                            return v___x_4800_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4795_);
                            crate::leanh::lean_dec(v_k_4794_);
                            v_t_4792_ = v_r_4796_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4793_);
                    crate::leanh::lean_dec_ref(v_inst_4791_);
                    v___x_4802_ = crate::leanh::lean_box(0);
                    return v___x_4802_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x3f(
    mut v_00_u03b1_4803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4804_: *mut crate::leanh::LeanObject,
    mut v_inst_4805_: *mut crate::leanh::LeanObject,
    mut v_t_4806_: *mut crate::leanh::LeanObject,
    mut v_k_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4808_ =
        l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_4805_, v_t_4806_, v_k_4807_);
    return v___x_4808_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey___redArg(
    mut v_inst_4809_: *mut crate::leanh::LeanObject,
    mut v_t_4810_: *mut crate::leanh::LeanObject,
    mut v_k_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4812_ = crate::leanh::lean_ctor_get(v_t_4810_, 1);
                crate::leanh::lean_inc_n(v_k_4812_, 2);
                v_l_4813_ = crate::leanh::lean_ctor_get(v_t_4810_, 3);
                crate::leanh::lean_inc(v_l_4813_);
                v_r_4814_ = crate::leanh::lean_ctor_get(v_t_4810_, 4);
                crate::leanh::lean_inc(v_r_4814_);
                crate::leanh::lean_dec(v_t_4810_);
                crate::leanh::lean_inc_ref(v_inst_4809_);
                crate::leanh::lean_inc(v_k_4811_);
                v___x_4815_ = crate::leanh::lean_apply_2(v_inst_4809_, v_k_4811_, v_k_4812_);
                v___x_4816_ = (crate::leanh::lean_unbox(v___x_4815_) as u8);
                match v___x_4816_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_4814_);
                        crate::leanh::lean_dec(v_k_4812_);
                        v_t_4810_ = v_l_4813_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_4814_);
                        crate::leanh::lean_dec(v_l_4813_);
                        crate::leanh::lean_dec(v_k_4811_);
                        crate::leanh::lean_dec_ref(v_inst_4809_);
                        return v_k_4812_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_4813_);
                        crate::leanh::lean_dec(v_k_4812_);
                        v_t_4810_ = v_r_4814_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey(
    mut v_00_u03b1_4819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4820_: *mut crate::leanh::LeanObject,
    mut v_inst_4821_: *mut crate::leanh::LeanObject,
    mut v_t_4822_: *mut crate::leanh::LeanObject,
    mut v_k_4823_: *mut crate::leanh::LeanObject,
    mut v_hlk_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4825_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_4821_, v_t_4822_, v_k_4823_);
    return v___x_4825_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2;
    v___x_4828_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_4829_ = crate::leanh::lean_unsigned_to_nat(186);
    v___x_4830_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0;
    v___x_4831_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_4832_ = l_mkPanicMessageWithDecl(
        v___x_4831_,
        v___x_4830_,
        v___x_4829_,
        v___x_4828_,
        v___x_4827_,
    );
    return v___x_4832_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
    mut v_inst_4833_: *mut crate::leanh::LeanObject,
    mut v_t_4834_: *mut crate::leanh::LeanObject,
    mut v_k_4835_: *mut crate::leanh::LeanObject,
    mut v_inst_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4834_) == 0 {
                    v_k_4837_ = crate::leanh::lean_ctor_get(v_t_4834_, 1);
                    crate::leanh::lean_inc_n(v_k_4837_, 2);
                    v_l_4838_ = crate::leanh::lean_ctor_get(v_t_4834_, 3);
                    crate::leanh::lean_inc(v_l_4838_);
                    v_r_4839_ = crate::leanh::lean_ctor_get(v_t_4834_, 4);
                    crate::leanh::lean_inc(v_r_4839_);
                    crate::leanh::lean_dec_ref_known(v_t_4834_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4833_);
                    crate::leanh::lean_inc(v_k_4835_);
                    v___x_4840_ = crate::leanh::lean_apply_2(v_inst_4833_, v_k_4835_, v_k_4837_);
                    v___x_4841_ = (crate::leanh::lean_unbox(v___x_4840_) as u8);
                    match v___x_4841_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4839_);
                            crate::leanh::lean_dec(v_k_4837_);
                            v_t_4834_ = v_l_4838_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4839_);
                            crate::leanh::lean_dec(v_l_4838_);
                            crate::leanh::lean_dec(v_k_4835_);
                            crate::leanh::lean_dec_ref(v_inst_4833_);
                            return v_k_4837_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4838_);
                            crate::leanh::lean_dec(v_k_4837_);
                            v_t_4834_ = v_r_4839_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4835_);
                    crate::leanh::lean_dec_ref(v_inst_4833_);
                    v___x_4844_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1,
                    );
                    v___x_4845_ = l_panic___redArg(v_inst_4836_, v___x_4844_);
                    return v___x_4845_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(
    mut v_inst_4846_: *mut crate::leanh::LeanObject,
    mut v_t_4847_: *mut crate::leanh::LeanObject,
    mut v_k_4848_: *mut crate::leanh::LeanObject,
    mut v_inst_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4850_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_inst_4846_,
        v_t_4847_,
        v_k_4848_,
        v_inst_4849_,
    );
    crate::leanh::lean_dec(v_inst_4849_);
    return v_res_4850_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21(
    mut v_00_u03b1_4851_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4852_: *mut crate::leanh::LeanObject,
    mut v_inst_4853_: *mut crate::leanh::LeanObject,
    mut v_t_4854_: *mut crate::leanh::LeanObject,
    mut v_k_4855_: *mut crate::leanh::LeanObject,
    mut v_inst_4856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(
        v_inst_4853_,
        v_t_4854_,
        v_k_4855_,
        v_inst_4856_,
    );
    return v___x_4857_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(
    mut v_00_u03b1_4858_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4859_: *mut crate::leanh::LeanObject,
    mut v_inst_4860_: *mut crate::leanh::LeanObject,
    mut v_t_4861_: *mut crate::leanh::LeanObject,
    mut v_k_4862_: *mut crate::leanh::LeanObject,
    mut v_inst_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4864_ = l_Std_DTreeMap_Internal_Impl_getKey_x21(
        v_00_u03b1_4858_,
        v_00_u03b2_4859_,
        v_inst_4860_,
        v_t_4861_,
        v_k_4862_,
        v_inst_4863_,
    );
    crate::leanh::lean_dec(v_inst_4863_);
    return v_res_4864_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
    mut v_inst_4865_: *mut crate::leanh::LeanObject,
    mut v_t_4866_: *mut crate::leanh::LeanObject,
    mut v_k_4867_: *mut crate::leanh::LeanObject,
    mut v_fallback_4868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4866_) == 0 {
                    v_k_4869_ = crate::leanh::lean_ctor_get(v_t_4866_, 1);
                    crate::leanh::lean_inc_n(v_k_4869_, 2);
                    v_l_4870_ = crate::leanh::lean_ctor_get(v_t_4866_, 3);
                    crate::leanh::lean_inc(v_l_4870_);
                    v_r_4871_ = crate::leanh::lean_ctor_get(v_t_4866_, 4);
                    crate::leanh::lean_inc(v_r_4871_);
                    crate::leanh::lean_dec_ref_known(v_t_4866_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4865_);
                    crate::leanh::lean_inc(v_k_4867_);
                    v___x_4872_ = crate::leanh::lean_apply_2(v_inst_4865_, v_k_4867_, v_k_4869_);
                    v___x_4873_ = (crate::leanh::lean_unbox(v___x_4872_) as u8);
                    match v___x_4873_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4871_);
                            crate::leanh::lean_dec(v_k_4869_);
                            v_t_4866_ = v_l_4870_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4871_);
                            crate::leanh::lean_dec(v_l_4870_);
                            crate::leanh::lean_dec(v_k_4867_);
                            crate::leanh::lean_dec_ref(v_inst_4865_);
                            return v_k_4869_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4870_);
                            crate::leanh::lean_dec(v_k_4869_);
                            v_t_4866_ = v_r_4871_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4867_);
                    crate::leanh::lean_dec_ref(v_inst_4865_);
                    crate::leanh::lean_inc(v_fallback_4868_);
                    return v_fallback_4868_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(
    mut v_inst_4876_: *mut crate::leanh::LeanObject,
    mut v_t_4877_: *mut crate::leanh::LeanObject,
    mut v_k_4878_: *mut crate::leanh::LeanObject,
    mut v_fallback_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4880_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_inst_4876_,
        v_t_4877_,
        v_k_4878_,
        v_fallback_4879_,
    );
    crate::leanh::lean_dec(v_fallback_4879_);
    return v_res_4880_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD(
    mut v_00_u03b1_4881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4882_: *mut crate::leanh::LeanObject,
    mut v_inst_4883_: *mut crate::leanh::LeanObject,
    mut v_t_4884_: *mut crate::leanh::LeanObject,
    mut v_k_4885_: *mut crate::leanh::LeanObject,
    mut v_fallback_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(
        v_inst_4883_,
        v_t_4884_,
        v_k_4885_,
        v_fallback_4886_,
    );
    return v___x_4887_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(
    mut v_00_u03b1_4888_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4889_: *mut crate::leanh::LeanObject,
    mut v_inst_4890_: *mut crate::leanh::LeanObject,
    mut v_t_4891_: *mut crate::leanh::LeanObject,
    mut v_k_4892_: *mut crate::leanh::LeanObject,
    mut v_fallback_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Std_DTreeMap_Internal_Impl_getKeyD(
        v_00_u03b1_4888_,
        v_00_u03b2_4889_,
        v_inst_4890_,
        v_t_4891_,
        v_k_4892_,
        v_fallback_4893_,
    );
    crate::leanh::lean_dec(v_fallback_4893_);
    return v_res_4894_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
    mut v_inst_4895_: *mut crate::leanh::LeanObject,
    mut v_t_4896_: *mut crate::leanh::LeanObject,
    mut v_k_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4896_) == 0 {
                    v_k_4898_ = crate::leanh::lean_ctor_get(v_t_4896_, 1);
                    crate::leanh::lean_inc(v_k_4898_);
                    v_v_4899_ = crate::leanh::lean_ctor_get(v_t_4896_, 2);
                    crate::leanh::lean_inc(v_v_4899_);
                    v_l_4900_ = crate::leanh::lean_ctor_get(v_t_4896_, 3);
                    crate::leanh::lean_inc(v_l_4900_);
                    v_r_4901_ = crate::leanh::lean_ctor_get(v_t_4896_, 4);
                    crate::leanh::lean_inc(v_r_4901_);
                    crate::leanh::lean_dec_ref_known(v_t_4896_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4895_);
                    crate::leanh::lean_inc(v_k_4897_);
                    v___x_4902_ = crate::leanh::lean_apply_2(v_inst_4895_, v_k_4897_, v_k_4898_);
                    v___x_4903_ = (crate::leanh::lean_unbox(v___x_4902_) as u8);
                    match v___x_4903_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4901_);
                            crate::leanh::lean_dec(v_v_4899_);
                            v_t_4896_ = v_l_4900_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4901_);
                            crate::leanh::lean_dec(v_l_4900_);
                            crate::leanh::lean_dec(v_k_4897_);
                            crate::leanh::lean_dec_ref(v_inst_4895_);
                            v___x_4905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4905_, 0, v_v_4899_);
                            return v___x_4905_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4900_);
                            crate::leanh::lean_dec(v_v_4899_);
                            v_t_4896_ = v_r_4901_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4897_);
                    crate::leanh::lean_dec_ref(v_inst_4895_);
                    v___x_4907_ = crate::leanh::lean_box(0);
                    return v___x_4907_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f(
    mut v_00_u03b1_4908_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4909_: *mut crate::leanh::LeanObject,
    mut v_inst_4910_: *mut crate::leanh::LeanObject,
    mut v_t_4911_: *mut crate::leanh::LeanObject,
    mut v_k_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4913_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_4910_, v_t_4911_, v_k_4912_);
    return v___x_4913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get___redArg(
    mut v_inst_4914_: *mut crate::leanh::LeanObject,
    mut v_t_4915_: *mut crate::leanh::LeanObject,
    mut v_k_4916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4917_ = crate::leanh::lean_ctor_get(v_t_4915_, 1);
                crate::leanh::lean_inc(v_k_4917_);
                v_v_4918_ = crate::leanh::lean_ctor_get(v_t_4915_, 2);
                crate::leanh::lean_inc(v_v_4918_);
                v_l_4919_ = crate::leanh::lean_ctor_get(v_t_4915_, 3);
                crate::leanh::lean_inc(v_l_4919_);
                v_r_4920_ = crate::leanh::lean_ctor_get(v_t_4915_, 4);
                crate::leanh::lean_inc(v_r_4920_);
                crate::leanh::lean_dec(v_t_4915_);
                crate::leanh::lean_inc_ref(v_inst_4914_);
                crate::leanh::lean_inc(v_k_4916_);
                v___x_4921_ = crate::leanh::lean_apply_2(v_inst_4914_, v_k_4916_, v_k_4917_);
                v___x_4922_ = (crate::leanh::lean_unbox(v___x_4921_) as u8);
                match v___x_4922_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_4920_);
                        crate::leanh::lean_dec(v_v_4918_);
                        v_t_4915_ = v_l_4919_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_4920_);
                        crate::leanh::lean_dec(v_l_4919_);
                        crate::leanh::lean_dec(v_k_4916_);
                        crate::leanh::lean_dec_ref(v_inst_4914_);
                        return v_v_4918_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_4919_);
                        crate::leanh::lean_dec(v_v_4918_);
                        v_t_4915_ = v_r_4920_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get(
    mut v_00_u03b1_4925_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4926_: *mut crate::leanh::LeanObject,
    mut v_inst_4927_: *mut crate::leanh::LeanObject,
    mut v_t_4928_: *mut crate::leanh::LeanObject,
    mut v_k_4929_: *mut crate::leanh::LeanObject,
    mut v_hlk_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4931_ =
        l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_4927_, v_t_4928_, v_k_4929_);
    return v___x_4931_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4933_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2;
    v___x_4934_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_4935_ = crate::leanh::lean_unsigned_to_nat(227);
    v___x_4936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0;
    v___x_4937_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_4938_ = l_mkPanicMessageWithDecl(
        v___x_4937_,
        v___x_4936_,
        v___x_4935_,
        v___x_4934_,
        v___x_4933_,
    );
    return v___x_4938_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
    mut v_inst_4939_: *mut crate::leanh::LeanObject,
    mut v_inst_4940_: *mut crate::leanh::LeanObject,
    mut v_t_4941_: *mut crate::leanh::LeanObject,
    mut v_k_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4941_) == 0 {
                    v_k_4943_ = crate::leanh::lean_ctor_get(v_t_4941_, 1);
                    crate::leanh::lean_inc(v_k_4943_);
                    v_v_4944_ = crate::leanh::lean_ctor_get(v_t_4941_, 2);
                    crate::leanh::lean_inc(v_v_4944_);
                    v_l_4945_ = crate::leanh::lean_ctor_get(v_t_4941_, 3);
                    crate::leanh::lean_inc(v_l_4945_);
                    v_r_4946_ = crate::leanh::lean_ctor_get(v_t_4941_, 4);
                    crate::leanh::lean_inc(v_r_4946_);
                    crate::leanh::lean_dec_ref_known(v_t_4941_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4939_);
                    crate::leanh::lean_inc(v_k_4942_);
                    v___x_4947_ = crate::leanh::lean_apply_2(v_inst_4939_, v_k_4942_, v_k_4943_);
                    v___x_4948_ = (crate::leanh::lean_unbox(v___x_4947_) as u8);
                    match v___x_4948_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4946_);
                            crate::leanh::lean_dec(v_v_4944_);
                            v_t_4941_ = v_l_4945_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4946_);
                            crate::leanh::lean_dec(v_l_4945_);
                            crate::leanh::lean_dec(v_k_4942_);
                            crate::leanh::lean_dec_ref(v_inst_4939_);
                            return v_v_4944_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4945_);
                            crate::leanh::lean_dec(v_v_4944_);
                            v_t_4941_ = v_r_4946_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4942_);
                    crate::leanh::lean_dec_ref(v_inst_4939_);
                    v___x_4951_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1,
                    );
                    v___x_4952_ = l_panic___redArg(v_inst_4940_, v___x_4951_);
                    return v___x_4952_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(
    mut v_inst_4953_: *mut crate::leanh::LeanObject,
    mut v_inst_4954_: *mut crate::leanh::LeanObject,
    mut v_t_4955_: *mut crate::leanh::LeanObject,
    mut v_k_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_inst_4953_,
        v_inst_4954_,
        v_t_4955_,
        v_k_4956_,
    );
    crate::leanh::lean_dec(v_inst_4954_);
    return v_res_4957_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21(
    mut v_00_u03b1_4958_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4959_: *mut crate::leanh::LeanObject,
    mut v_inst_4960_: *mut crate::leanh::LeanObject,
    mut v_inst_4961_: *mut crate::leanh::LeanObject,
    mut v_t_4962_: *mut crate::leanh::LeanObject,
    mut v_k_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4964_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(
        v_inst_4960_,
        v_inst_4961_,
        v_t_4962_,
        v_k_4963_,
    );
    return v___x_4964_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(
    mut v_00_u03b1_4965_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4966_: *mut crate::leanh::LeanObject,
    mut v_inst_4967_: *mut crate::leanh::LeanObject,
    mut v_inst_4968_: *mut crate::leanh::LeanObject,
    mut v_t_4969_: *mut crate::leanh::LeanObject,
    mut v_k_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21(
        v_00_u03b1_4965_,
        v_00_u03b4_4966_,
        v_inst_4967_,
        v_inst_4968_,
        v_t_4969_,
        v_k_4970_,
    );
    crate::leanh::lean_dec(v_inst_4968_);
    return v_res_4971_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
    mut v_inst_4972_: *mut crate::leanh::LeanObject,
    mut v_t_4973_: *mut crate::leanh::LeanObject,
    mut v_k_4974_: *mut crate::leanh::LeanObject,
    mut v_fallback_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4973_) == 0 {
                    v_k_4976_ = crate::leanh::lean_ctor_get(v_t_4973_, 1);
                    crate::leanh::lean_inc(v_k_4976_);
                    v_v_4977_ = crate::leanh::lean_ctor_get(v_t_4973_, 2);
                    crate::leanh::lean_inc(v_v_4977_);
                    v_l_4978_ = crate::leanh::lean_ctor_get(v_t_4973_, 3);
                    crate::leanh::lean_inc(v_l_4978_);
                    v_r_4979_ = crate::leanh::lean_ctor_get(v_t_4973_, 4);
                    crate::leanh::lean_inc(v_r_4979_);
                    crate::leanh::lean_dec_ref_known(v_t_4973_, 5);
                    crate::leanh::lean_inc_ref(v_inst_4972_);
                    crate::leanh::lean_inc(v_k_4974_);
                    v___x_4980_ = crate::leanh::lean_apply_2(v_inst_4972_, v_k_4974_, v_k_4976_);
                    v___x_4981_ = (crate::leanh::lean_unbox(v___x_4980_) as u8);
                    match v___x_4981_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_4979_);
                            crate::leanh::lean_dec(v_v_4977_);
                            v_t_4973_ = v_l_4978_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_4979_);
                            crate::leanh::lean_dec(v_l_4978_);
                            crate::leanh::lean_dec(v_k_4974_);
                            crate::leanh::lean_dec_ref(v_inst_4972_);
                            return v_v_4977_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_4978_);
                            crate::leanh::lean_dec(v_v_4977_);
                            v_t_4973_ = v_r_4979_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4974_);
                    crate::leanh::lean_dec_ref(v_inst_4972_);
                    crate::leanh::lean_inc(v_fallback_4975_);
                    return v_fallback_4975_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(
    mut v_inst_4984_: *mut crate::leanh::LeanObject,
    mut v_t_4985_: *mut crate::leanh::LeanObject,
    mut v_k_4986_: *mut crate::leanh::LeanObject,
    mut v_fallback_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4988_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_inst_4984_,
        v_t_4985_,
        v_k_4986_,
        v_fallback_4987_,
    );
    crate::leanh::lean_dec(v_fallback_4987_);
    return v_res_4988_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD(
    mut v_00_u03b1_4989_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4990_: *mut crate::leanh::LeanObject,
    mut v_inst_4991_: *mut crate::leanh::LeanObject,
    mut v_t_4992_: *mut crate::leanh::LeanObject,
    mut v_k_4993_: *mut crate::leanh::LeanObject,
    mut v_fallback_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4995_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v_inst_4991_,
        v_t_4992_,
        v_k_4993_,
        v_fallback_4994_,
    );
    return v___x_4995_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(
    mut v_00_u03b1_4996_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_4997_: *mut crate::leanh::LeanObject,
    mut v_inst_4998_: *mut crate::leanh::LeanObject,
    mut v_t_4999_: *mut crate::leanh::LeanObject,
    mut v_k_5000_: *mut crate::leanh::LeanObject,
    mut v_fallback_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5002_ = l_Std_DTreeMap_Internal_Impl_Const_getD(
        v_00_u03b1_4996_,
        v_00_u03b4_4997_,
        v_inst_4998_,
        v_t_4999_,
        v_k_5000_,
        v_fallback_5001_,
    );
    crate::leanh::lean_dec(v_fallback_5001_);
    return v_res_5002_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(
    mut v_f_5003_: *mut crate::leanh::LeanObject,
    mut v_k_5004_: *mut crate::leanh::LeanObject,
    mut v_v_5005_: *mut crate::leanh::LeanObject,
    mut v_toBind_5006_: *mut crate::leanh::LeanObject,
    mut v___f_5007_: *mut crate::leanh::LeanObject,
    mut v_left_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5009_ = crate::leanh::lean_apply_3(v_f_5003_, v_left_5008_, v_k_5004_, v_v_5005_);
    v___x_5010_ = crate::leanh::lean_apply_4(
        v_toBind_5006_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5009_,
        v___f_5007_,
    );
    return v___x_5010_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
    mut v_inst_5011_: *mut crate::leanh::LeanObject,
    mut v_f_5012_: *mut crate::leanh::LeanObject,
    mut v_init_5013_: *mut crate::leanh::LeanObject,
    mut v_x_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5014_) == 0 {
        let mut v_toBind_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_5015_ = crate::leanh::lean_ctor_get(v_inst_5011_, 1);
        crate::leanh::lean_inc_n(v_toBind_5015_, 2);
        v_k_5016_ = crate::leanh::lean_ctor_get(v_x_5014_, 1);
        crate::leanh::lean_inc(v_k_5016_);
        v_v_5017_ = crate::leanh::lean_ctor_get(v_x_5014_, 2);
        crate::leanh::lean_inc(v_v_5017_);
        v_l_5018_ = crate::leanh::lean_ctor_get(v_x_5014_, 3);
        crate::leanh::lean_inc(v_l_5018_);
        v_r_5019_ = crate::leanh::lean_ctor_get(v_x_5014_, 4);
        crate::leanh::lean_inc(v_r_5019_);
        crate::leanh::lean_dec_ref_known(v_x_5014_, 5);
        crate::leanh::lean_inc_n(v_f_5012_, 2);
        crate::leanh::lean_inc_ref(v_inst_5011_);
        v___f_5020_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_5020_, 0, v_inst_5011_);
        crate::leanh::lean_closure_set(v___f_5020_, 1, v_f_5012_);
        crate::leanh::lean_closure_set(v___f_5020_, 2, v_r_5019_);
        v___f_5021_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_5021_, 0, v_f_5012_);
        crate::leanh::lean_closure_set(v___f_5021_, 1, v_k_5016_);
        crate::leanh::lean_closure_set(v___f_5021_, 2, v_v_5017_);
        crate::leanh::lean_closure_set(v___f_5021_, 3, v_toBind_5015_);
        crate::leanh::lean_closure_set(v___f_5021_, 4, v___f_5020_);
        v___x_5022_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
            v_inst_5011_,
            v_f_5012_,
            v_init_5013_,
            v_l_5018_,
        );
        v___x_5023_ = crate::leanh::lean_apply_4(
            v_toBind_5015_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5022_,
            v___f_5021_,
        );
        return v___x_5023_;
    } else {
        let mut v_toApplicative_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5024_ = crate::leanh::lean_ctor_get(v_inst_5011_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5024_);
        crate::leanh::lean_dec(v_f_5012_);
        crate::leanh::lean_dec_ref(v_inst_5011_);
        v_toPure_5025_ = crate::leanh::lean_ctor_get(v_toApplicative_5024_, 1);
        crate::leanh::lean_inc(v_toPure_5025_);
        crate::leanh::lean_dec_ref(v_toApplicative_5024_);
        v___x_5026_ =
            crate::leanh::lean_apply_2(v_toPure_5025_, crate::leanh::lean_box(0), v_init_5013_);
        return v___x_5026_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(
    mut v_inst_5027_: *mut crate::leanh::LeanObject,
    mut v_f_5028_: *mut crate::leanh::LeanObject,
    mut v_r_5029_: *mut crate::leanh::LeanObject,
    mut v_middle_5030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5031_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_5027_,
        v_f_5028_,
        v_middle_5030_,
        v_r_5029_,
    );
    return v___x_5031_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM(
    mut v_00_u03b1_5032_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5034_: *mut crate::leanh::LeanObject,
    mut v_m_5035_: *mut crate::leanh::LeanObject,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v_f_5037_: *mut crate::leanh::LeanObject,
    mut v_init_5038_: *mut crate::leanh::LeanObject,
    mut v_x_5039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_5036_,
        v_f_5037_,
        v_init_5038_,
        v_x_5039_,
    );
    return v___x_5040_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(
    mut v_f_5041_: *mut crate::leanh::LeanObject,
    mut v_x1_5042_: *mut crate::leanh::LeanObject,
    mut v_x2_5043_: *mut crate::leanh::LeanObject,
    mut v_x3_5044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = crate::leanh::lean_apply_3(v_f_5041_, v_x1_5042_, v_x2_5043_, v_x3_5044_);
    return v___x_5045_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___redArg(
    mut v_f_5065_: *mut crate::leanh::LeanObject,
    mut v_init_5066_: *mut crate::leanh::LeanObject,
    mut v_t_5067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5068_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5068_, 0, v_f_5065_);
    v___x_5069_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5070_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v___x_5069_,
        v___f_5068_,
        v_init_5066_,
        v_t_5067_,
    );
    return v___x_5070_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl(
    mut v_00_u03b1_5071_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5072_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5073_: *mut crate::leanh::LeanObject,
    mut v_f_5074_: *mut crate::leanh::LeanObject,
    mut v_init_5075_: *mut crate::leanh::LeanObject,
    mut v_t_5076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5077_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_5074_, v_init_5075_, v_t_5076_);
    return v___x_5077_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(
    mut v_f_5078_: *mut crate::leanh::LeanObject,
    mut v_k_5079_: *mut crate::leanh::LeanObject,
    mut v_v_5080_: *mut crate::leanh::LeanObject,
    mut v_toBind_5081_: *mut crate::leanh::LeanObject,
    mut v___f_5082_: *mut crate::leanh::LeanObject,
    mut v_right_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5084_ = crate::leanh::lean_apply_3(v_f_5078_, v_k_5079_, v_v_5080_, v_right_5083_);
    v___x_5085_ = crate::leanh::lean_apply_4(
        v_toBind_5081_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5084_,
        v___f_5082_,
    );
    return v___x_5085_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
    mut v_inst_5086_: *mut crate::leanh::LeanObject,
    mut v_f_5087_: *mut crate::leanh::LeanObject,
    mut v_init_5088_: *mut crate::leanh::LeanObject,
    mut v_x_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5089_) == 0 {
        let mut v_toBind_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_5090_ = crate::leanh::lean_ctor_get(v_inst_5086_, 1);
        crate::leanh::lean_inc_n(v_toBind_5090_, 2);
        v_k_5091_ = crate::leanh::lean_ctor_get(v_x_5089_, 1);
        crate::leanh::lean_inc(v_k_5091_);
        v_v_5092_ = crate::leanh::lean_ctor_get(v_x_5089_, 2);
        crate::leanh::lean_inc(v_v_5092_);
        v_l_5093_ = crate::leanh::lean_ctor_get(v_x_5089_, 3);
        crate::leanh::lean_inc(v_l_5093_);
        v_r_5094_ = crate::leanh::lean_ctor_get(v_x_5089_, 4);
        crate::leanh::lean_inc(v_r_5094_);
        crate::leanh::lean_dec_ref_known(v_x_5089_, 5);
        crate::leanh::lean_inc_n(v_f_5087_, 2);
        crate::leanh::lean_inc_ref(v_inst_5086_);
        v___f_5095_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_5095_, 0, v_inst_5086_);
        crate::leanh::lean_closure_set(v___f_5095_, 1, v_f_5087_);
        crate::leanh::lean_closure_set(v___f_5095_, 2, v_l_5093_);
        v___f_5096_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_5096_, 0, v_f_5087_);
        crate::leanh::lean_closure_set(v___f_5096_, 1, v_k_5091_);
        crate::leanh::lean_closure_set(v___f_5096_, 2, v_v_5092_);
        crate::leanh::lean_closure_set(v___f_5096_, 3, v_toBind_5090_);
        crate::leanh::lean_closure_set(v___f_5096_, 4, v___f_5095_);
        v___x_5097_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
            v_inst_5086_,
            v_f_5087_,
            v_init_5088_,
            v_r_5094_,
        );
        v___x_5098_ = crate::leanh::lean_apply_4(
            v_toBind_5090_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5097_,
            v___f_5096_,
        );
        return v___x_5098_;
    } else {
        let mut v_toApplicative_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5099_ = crate::leanh::lean_ctor_get(v_inst_5086_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5099_);
        crate::leanh::lean_dec(v_f_5087_);
        crate::leanh::lean_dec_ref(v_inst_5086_);
        v_toPure_5100_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 1);
        crate::leanh::lean_inc(v_toPure_5100_);
        crate::leanh::lean_dec_ref(v_toApplicative_5099_);
        v___x_5101_ =
            crate::leanh::lean_apply_2(v_toPure_5100_, crate::leanh::lean_box(0), v_init_5088_);
        return v___x_5101_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(
    mut v_inst_5102_: *mut crate::leanh::LeanObject,
    mut v_f_5103_: *mut crate::leanh::LeanObject,
    mut v_l_5104_: *mut crate::leanh::LeanObject,
    mut v_middle_5105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_5102_,
        v_f_5103_,
        v_middle_5105_,
        v_l_5104_,
    );
    return v___x_5106_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM(
    mut v_00_u03b1_5107_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5109_: *mut crate::leanh::LeanObject,
    mut v_m_5110_: *mut crate::leanh::LeanObject,
    mut v_inst_5111_: *mut crate::leanh::LeanObject,
    mut v_f_5112_: *mut crate::leanh::LeanObject,
    mut v_init_5113_: *mut crate::leanh::LeanObject,
    mut v_x_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5115_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v_inst_5111_,
        v_f_5112_,
        v_init_5113_,
        v_x_5114_,
    );
    return v___x_5115_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldr___redArg(
    mut v_f_5116_: *mut crate::leanh::LeanObject,
    mut v_init_5117_: *mut crate::leanh::LeanObject,
    mut v_t_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5119_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5119_, 0, v_f_5116_);
    v___x_5120_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5121_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5120_,
        v___f_5119_,
        v_init_5117_,
        v_t_5118_,
    );
    return v___x_5121_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldr(
    mut v_00_u03b1_5122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5124_: *mut crate::leanh::LeanObject,
    mut v_f_5125_: *mut crate::leanh::LeanObject,
    mut v_init_5126_: *mut crate::leanh::LeanObject,
    mut v_t_5127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5128_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5128_, 0, v_f_5125_);
    v___x_5129_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5130_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5129_,
        v___f_5128_,
        v_init_5126_,
        v_t_5127_,
    );
    return v___x_5130_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(
    mut v_f_5131_: *mut crate::leanh::LeanObject,
    mut v_x_5132_: *mut crate::leanh::LeanObject,
    mut v_k_5133_: *mut crate::leanh::LeanObject,
    mut v_v_5134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = crate::leanh::lean_apply_2(v_f_5131_, v_k_5133_, v_v_5134_);
    return v___x_5135_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forM___redArg(
    mut v_inst_5136_: *mut crate::leanh::LeanObject,
    mut v_f_5137_: *mut crate::leanh::LeanObject,
    mut v_t_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5139_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5139_, 0, v_f_5137_);
    v___x_5140_ = crate::leanh::lean_box(0);
    v___x_5141_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_5136_,
        v___f_5139_,
        v___x_5140_,
        v_t_5138_,
    );
    return v___x_5141_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forM(
    mut v_00_u03b1_5142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5143_: *mut crate::leanh::LeanObject,
    mut v_m_5144_: *mut crate::leanh::LeanObject,
    mut v_inst_5145_: *mut crate::leanh::LeanObject,
    mut v_f_5146_: *mut crate::leanh::LeanObject,
    mut v_t_5147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5148_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5148_, 0, v_f_5146_);
    v___x_5149_ = crate::leanh::lean_box(0);
    v___x_5150_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
        v_inst_5145_,
        v___f_5148_,
        v___x_5149_,
        v_t_5147_,
    );
    return v___x_5150_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(
    mut v_toPure_5151_: *mut crate::leanh::LeanObject,
    mut v_d_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5153_, 0, v_d_5152_);
    v___x_5154_ =
        crate::leanh::lean_apply_2(v_toPure_5151_, crate::leanh::lean_box(0), v___x_5153_);
    return v___x_5154_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(
    mut v___f_5155_: *mut crate::leanh::LeanObject,
    mut v_f_5156_: *mut crate::leanh::LeanObject,
    mut v_k_5157_: *mut crate::leanh::LeanObject,
    mut v_v_5158_: *mut crate::leanh::LeanObject,
    mut v_toBind_5159_: *mut crate::leanh::LeanObject,
    mut v___f_5160_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_5161_) == 0 {
        let mut v_a_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_5160_);
        crate::leanh::lean_dec(v_toBind_5159_);
        crate::leanh::lean_dec(v_v_5158_);
        crate::leanh::lean_dec(v_k_5157_);
        crate::leanh::lean_dec(v_f_5156_);
        v_a_5162_ = crate::leanh::lean_ctor_get(v_____do__lift_5161_, 0);
        crate::leanh::lean_inc(v_a_5162_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5161_, 1);
        v___x_5163_ = crate::leanh::lean_apply_1(v___f_5155_, v_a_5162_);
        return v___x_5163_;
    } else {
        let mut v_a_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_5155_);
        v_a_5164_ = crate::leanh::lean_ctor_get(v_____do__lift_5161_, 0);
        crate::leanh::lean_inc(v_a_5164_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5161_, 1);
        v___x_5165_ = crate::leanh::lean_apply_3(v_f_5156_, v_k_5157_, v_v_5158_, v_a_5164_);
        v___x_5166_ = crate::leanh::lean_apply_4(
            v_toBind_5159_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5165_,
            v___f_5160_,
        );
        return v___x_5166_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
    mut v_inst_5167_: *mut crate::leanh::LeanObject,
    mut v_f_5168_: *mut crate::leanh::LeanObject,
    mut v_init_5169_: *mut crate::leanh::LeanObject,
    mut v_x_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5170_) == 0 {
        let mut v_toApplicative_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5171_ = crate::leanh::lean_ctor_get(v_inst_5167_, 0);
        v_toBind_5172_ = crate::leanh::lean_ctor_get(v_inst_5167_, 1);
        crate::leanh::lean_inc_n(v_toBind_5172_, 2);
        v_toPure_5173_ = crate::leanh::lean_ctor_get(v_toApplicative_5171_, 1);
        v_k_5174_ = crate::leanh::lean_ctor_get(v_x_5170_, 1);
        crate::leanh::lean_inc(v_k_5174_);
        v_v_5175_ = crate::leanh::lean_ctor_get(v_x_5170_, 2);
        crate::leanh::lean_inc(v_v_5175_);
        v_l_5176_ = crate::leanh::lean_ctor_get(v_x_5170_, 3);
        crate::leanh::lean_inc(v_l_5176_);
        v_r_5177_ = crate::leanh::lean_ctor_get(v_x_5170_, 4);
        crate::leanh::lean_inc(v_r_5177_);
        crate::leanh::lean_dec_ref_known(v_x_5170_, 5);
        crate::leanh::lean_inc(v_toPure_5173_);
        v___f_5178_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5178_, 0, v_toPure_5173_);
        crate::leanh::lean_inc_n(v_f_5168_, 2);
        crate::leanh::lean_inc_ref(v_inst_5167_);
        crate::leanh::lean_inc_ref(v___f_5178_);
        v___f_5179_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5179_, 0, v___f_5178_);
        crate::leanh::lean_closure_set(v___f_5179_, 1, v_inst_5167_);
        crate::leanh::lean_closure_set(v___f_5179_, 2, v_f_5168_);
        crate::leanh::lean_closure_set(v___f_5179_, 3, v_r_5177_);
        v___f_5180_ = crate::leanh::lean_alloc_closure(
            l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2 as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_5180_, 0, v___f_5178_);
        crate::leanh::lean_closure_set(v___f_5180_, 1, v_f_5168_);
        crate::leanh::lean_closure_set(v___f_5180_, 2, v_k_5174_);
        crate::leanh::lean_closure_set(v___f_5180_, 3, v_v_5175_);
        crate::leanh::lean_closure_set(v___f_5180_, 4, v_toBind_5172_);
        crate::leanh::lean_closure_set(v___f_5180_, 5, v___f_5179_);
        v___x_5181_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
            v_inst_5167_,
            v_f_5168_,
            v_init_5169_,
            v_l_5176_,
        );
        v___x_5182_ = crate::leanh::lean_apply_4(
            v_toBind_5172_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5181_,
            v___f_5180_,
        );
        return v___x_5182_;
    } else {
        let mut v_toApplicative_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5183_ = crate::leanh::lean_ctor_get(v_inst_5167_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5183_);
        crate::leanh::lean_dec(v_f_5168_);
        crate::leanh::lean_dec_ref(v_inst_5167_);
        v_toPure_5184_ = crate::leanh::lean_ctor_get(v_toApplicative_5183_, 1);
        crate::leanh::lean_inc(v_toPure_5184_);
        crate::leanh::lean_dec_ref(v_toApplicative_5183_);
        v___x_5185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5185_, 0, v_init_5169_);
        v___x_5186_ =
            crate::leanh::lean_apply_2(v_toPure_5184_, crate::leanh::lean_box(0), v___x_5185_);
        return v___x_5186_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(
    mut v___f_5187_: *mut crate::leanh::LeanObject,
    mut v_inst_5188_: *mut crate::leanh::LeanObject,
    mut v_f_5189_: *mut crate::leanh::LeanObject,
    mut v_r_5190_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_5191_) == 0 {
        let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_r_5190_);
        crate::leanh::lean_dec(v_f_5189_);
        crate::leanh::lean_dec_ref(v_inst_5188_);
        v_a_5192_ = crate::leanh::lean_ctor_get(v_____do__lift_5191_, 0);
        crate::leanh::lean_inc(v_a_5192_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5191_, 1);
        v___x_5193_ = crate::leanh::lean_apply_1(v___f_5187_, v_a_5192_);
        return v___x_5193_;
    } else {
        let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_5187_);
        v_a_5194_ = crate::leanh::lean_ctor_get(v_____do__lift_5191_, 0);
        crate::leanh::lean_inc(v_a_5194_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5191_, 1);
        v___x_5195_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
            v_inst_5188_,
            v_f_5189_,
            v_a_5194_,
            v_r_5190_,
        );
        return v___x_5195_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep(
    mut v_00_u03b1_5196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5197_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5198_: *mut crate::leanh::LeanObject,
    mut v_m_5199_: *mut crate::leanh::LeanObject,
    mut v_inst_5200_: *mut crate::leanh::LeanObject,
    mut v_f_5201_: *mut crate::leanh::LeanObject,
    mut v_init_5202_: *mut crate::leanh::LeanObject,
    mut v_x_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5204_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_5200_,
        v_f_5201_,
        v_init_5202_,
        v_x_5203_,
    );
    return v___x_5204_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(
    mut v_toPure_5205_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_5207_ = crate::leanh::lean_ctor_get(v_____do__lift_5206_, 0);
    crate::leanh::lean_inc(v_a_5207_);
    crate::leanh::lean_dec_ref(v_____do__lift_5206_);
    v___x_5208_ = crate::leanh::lean_apply_2(v_toPure_5205_, crate::leanh::lean_box(0), v_a_5207_);
    return v___x_5208_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forIn___redArg(
    mut v_inst_5209_: *mut crate::leanh::LeanObject,
    mut v_f_5210_: *mut crate::leanh::LeanObject,
    mut v_init_5211_: *mut crate::leanh::LeanObject,
    mut v_t_5212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5213_ = crate::leanh::lean_ctor_get(v_inst_5209_, 0);
    v_toBind_5214_ = crate::leanh::lean_ctor_get(v_inst_5209_, 1);
    crate::leanh::lean_inc(v_toBind_5214_);
    v_toPure_5215_ = crate::leanh::lean_ctor_get(v_toApplicative_5213_, 1);
    crate::leanh::lean_inc(v_toPure_5215_);
    v___x_5216_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_5209_,
        v_f_5210_,
        v_init_5211_,
        v_t_5212_,
    );
    v___f_5217_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5217_, 0, v_toPure_5215_);
    v___x_5218_ = crate::leanh::lean_apply_4(
        v_toBind_5214_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5216_,
        v___f_5217_,
    );
    return v___x_5218_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forIn(
    mut v_00_u03b1_5219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_5221_: *mut crate::leanh::LeanObject,
    mut v_m_5222_: *mut crate::leanh::LeanObject,
    mut v_inst_5223_: *mut crate::leanh::LeanObject,
    mut v_f_5224_: *mut crate::leanh::LeanObject,
    mut v_init_5225_: *mut crate::leanh::LeanObject,
    mut v_t_5226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5227_ = crate::leanh::lean_ctor_get(v_inst_5223_, 0);
    v_toBind_5228_ = crate::leanh::lean_ctor_get(v_inst_5223_, 1);
    crate::leanh::lean_inc(v_toBind_5228_);
    v_toPure_5229_ = crate::leanh::lean_ctor_get(v_toApplicative_5227_, 1);
    crate::leanh::lean_inc(v_toPure_5229_);
    v___x_5230_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_5223_,
        v_f_5224_,
        v_init_5225_,
        v_t_5226_,
    );
    v___f_5231_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5231_, 0, v_toPure_5229_);
    v___x_5232_ = crate::leanh::lean_apply_4(
        v_toBind_5228_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5230_,
        v___f_5231_,
    );
    return v___x_5232_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(
    mut v_f_5233_: *mut crate::leanh::LeanObject,
    mut v_a_5234_: *mut crate::leanh::LeanObject,
    mut v_b_5235_: *mut crate::leanh::LeanObject,
    mut v_acc_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5237_, 0, v_a_5234_);
    crate::leanh::lean_ctor_set(v___x_5237_, 1, v_b_5235_);
    v___x_5238_ = crate::leanh::lean_apply_2(v_f_5233_, v___x_5237_, v_acc_5236_);
    return v___x_5238_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(
    mut v_inst_5239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5240_: *mut crate::leanh::LeanObject,
    mut v_m_5241_: *mut crate::leanh::LeanObject,
    mut v_init_5242_: *mut crate::leanh::LeanObject,
    mut v_f_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5244_ = crate::leanh::lean_ctor_get(v_inst_5239_, 0);
    v_toBind_5245_ = crate::leanh::lean_ctor_get(v_inst_5239_, 1);
    crate::leanh::lean_inc(v_toBind_5245_);
    v_toPure_5246_ = crate::leanh::lean_ctor_get(v_toApplicative_5244_, 1);
    crate::leanh::lean_inc(v_toPure_5246_);
    v___f_5247_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5247_, 0, v_f_5243_);
    v___x_5248_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_5239_,
        v___f_5247_,
        v_init_5242_,
        v_m_5241_,
    );
    v___f_5249_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5249_, 0, v_toPure_5246_);
    v___x_5250_ = crate::leanh::lean_apply_4(
        v_toBind_5245_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5248_,
        v___f_5249_,
    );
    return v___x_5250_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(
    mut v_inst_5251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5252_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5252_, 0, v_inst_5251_);
    return v___f_5252_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(
    mut v_00_u03b1_5253_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5254_: *mut crate::leanh::LeanObject,
    mut v_m_5255_: *mut crate::leanh::LeanObject,
    mut v_inst_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5257_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5257_, 0, v_inst_5256_);
    return v___f_5257_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(
    mut v_p_5258_: *mut crate::leanh::LeanObject,
    mut v___x_5259_: *mut crate::leanh::LeanObject,
    mut v___x_5260_: *mut crate::leanh::LeanObject,
    mut v_a_5261_: *mut crate::leanh::LeanObject,
    mut v_b_5262_: *mut crate::leanh::LeanObject,
    mut v_acc_5263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    v___x_5264_ = crate::leanh::lean_apply_2(v_p_5258_, v_a_5261_, v_b_5262_);
    v___x_5265_ = (crate::leanh::lean_unbox(v___x_5264_) as u8);
    if v___x_5265_ == 0 {
        let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5266_, 0, v___x_5259_);
        return v___x_5266_;
    } else {
        let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_5259_);
        v___x_5267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5267_, 0, v___x_5264_);
        v___x_5268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5267_);
        crate::leanh::lean_ctor_set(v___x_5268_, 1, v___x_5260_);
        v___x_5269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5269_, 0, v___x_5268_);
        return v___x_5269_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(
    mut v_p_5270_: *mut crate::leanh::LeanObject,
    mut v___x_5271_: *mut crate::leanh::LeanObject,
    mut v___x_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_b_5274_: *mut crate::leanh::LeanObject,
    mut v_acc_5275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5276_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(
        v_p_5270_,
        v___x_5271_,
        v___x_5272_,
        v_a_5273_,
        v_b_5274_,
        v_acc_5275_,
    );
    crate::leanh::lean_dec_ref(v_acc_5275_);
    return v_res_5276_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any___redArg(
    mut v_t_5280_: *mut crate::leanh::LeanObject,
    mut v_p_5281_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v_val_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5288_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
                v___x_5289_ = crate::leanh::lean_box(0);
                v___x_5290_ = l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0;
                v___f_5291_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5291_, 0, v_p_5281_);
                crate::leanh::lean_closure_set(v___f_5291_, 1, v___x_5290_);
                crate::leanh::lean_closure_set(v___f_5291_, 2, v___x_5289_);
                v___x_5292_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_5288_,
                    v___f_5291_,
                    v___x_5290_,
                    v_t_5280_,
                );
                v_a_5293_ = crate::leanh::lean_ctor_get(v___x_5292_, 0);
                crate::leanh::lean_inc(v_a_5293_);
                crate::leanh::lean_dec(v___x_5292_);
                v___y_5283_ = v_a_5293_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_5284_ = crate::leanh::lean_ctor_get(v___y_5283_, 0);
                crate::leanh::lean_inc(v_fst_5284_);
                crate::leanh::lean_dec_ref(v___y_5283_);
                if crate::leanh::lean_obj_tag(v_fst_5284_) == 0 {
                    v___x_5285_ = 0;
                    return v___x_5285_;
                } else {
                    v_val_5286_ = crate::leanh::lean_ctor_get(v_fst_5284_, 0);
                    crate::leanh::lean_inc(v_val_5286_);
                    crate::leanh::lean_dec_ref_known(v_fst_5284_, 1);
                    v___x_5287_ = (crate::leanh::lean_unbox(v_val_5286_) as u8);
                    crate::leanh::lean_dec(v_val_5286_);
                    return v___x_5287_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(
    mut v_t_5294_: *mut crate::leanh::LeanObject,
    mut v_p_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5296_: u8 = 0;
    let mut v_r_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5296_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_5294_, v_p_5295_);
    v_r_5297_ = crate::leanh::lean_box((v_res_5296_) as usize);
    return v_r_5297_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any(
    mut v_00_u03b1_5298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5299_: *mut crate::leanh::LeanObject,
    mut v_t_5300_: *mut crate::leanh::LeanObject,
    mut v_p_5301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v_val_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5308_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
                v___x_5309_ = crate::leanh::lean_box(0);
                v___x_5310_ = l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0;
                v___f_5311_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5311_, 0, v_p_5301_);
                crate::leanh::lean_closure_set(v___f_5311_, 1, v___x_5310_);
                crate::leanh::lean_closure_set(v___f_5311_, 2, v___x_5309_);
                v___x_5312_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_5308_,
                    v___f_5311_,
                    v___x_5310_,
                    v_t_5300_,
                );
                v_a_5313_ = crate::leanh::lean_ctor_get(v___x_5312_, 0);
                crate::leanh::lean_inc(v_a_5313_);
                crate::leanh::lean_dec(v___x_5312_);
                v___y_5303_ = v_a_5313_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_5304_ = crate::leanh::lean_ctor_get(v___y_5303_, 0);
                crate::leanh::lean_inc(v_fst_5304_);
                crate::leanh::lean_dec_ref(v___y_5303_);
                if crate::leanh::lean_obj_tag(v_fst_5304_) == 0 {
                    v___x_5305_ = 0;
                    return v___x_5305_;
                } else {
                    v_val_5306_ = crate::leanh::lean_ctor_get(v_fst_5304_, 0);
                    crate::leanh::lean_inc(v_val_5306_);
                    crate::leanh::lean_dec_ref_known(v_fst_5304_, 1);
                    v___x_5307_ = (crate::leanh::lean_unbox(v_val_5306_) as u8);
                    crate::leanh::lean_dec(v_val_5306_);
                    return v___x_5307_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_any___boxed(
    mut v_00_u03b1_5314_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5315_: *mut crate::leanh::LeanObject,
    mut v_t_5316_: *mut crate::leanh::LeanObject,
    mut v_p_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5318_: u8 = 0;
    let mut v_r_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5318_ =
        l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_5314_, v_00_u03b2_5315_, v_t_5316_, v_p_5317_);
    v_r_5319_ = crate::leanh::lean_box((v_res_5318_) as usize);
    return v_r_5319_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(
    mut v_p_5320_: *mut crate::leanh::LeanObject,
    mut v___x_5321_: *mut crate::leanh::LeanObject,
    mut v___x_5322_: *mut crate::leanh::LeanObject,
    mut v_a_5323_: *mut crate::leanh::LeanObject,
    mut v_b_5324_: *mut crate::leanh::LeanObject,
    mut v_acc_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: u8 = 0;
    v___x_5326_ = crate::leanh::lean_apply_2(v_p_5320_, v_a_5323_, v_b_5324_);
    v___x_5327_ = (crate::leanh::lean_unbox(v___x_5326_) as u8);
    if v___x_5327_ == 0 {
        let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_5322_);
        v___x_5328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5328_, 0, v___x_5326_);
        v___x_5329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5329_, 0, v___x_5328_);
        crate::leanh::lean_ctor_set(v___x_5329_, 1, v___x_5321_);
        v___x_5330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5330_, 0, v___x_5329_);
        return v___x_5330_;
    } else {
        let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5331_, 0, v___x_5322_);
        return v___x_5331_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(
    mut v_p_5332_: *mut crate::leanh::LeanObject,
    mut v___x_5333_: *mut crate::leanh::LeanObject,
    mut v___x_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
    mut v_b_5336_: *mut crate::leanh::LeanObject,
    mut v_acc_5337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5338_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(
        v_p_5332_,
        v___x_5333_,
        v___x_5334_,
        v_a_5335_,
        v_b_5336_,
        v_acc_5337_,
    );
    crate::leanh::lean_dec_ref(v_acc_5337_);
    return v_res_5338_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all___redArg(
    mut v_t_5339_: *mut crate::leanh::LeanObject,
    mut v_p_5340_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: u8 = 0;
    let mut v_val_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5347_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
                v___x_5348_ = crate::leanh::lean_box(0);
                v___x_5349_ = l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0;
                v___f_5350_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5350_, 0, v_p_5340_);
                crate::leanh::lean_closure_set(v___f_5350_, 1, v___x_5348_);
                crate::leanh::lean_closure_set(v___f_5350_, 2, v___x_5349_);
                v___x_5351_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_5347_,
                    v___f_5350_,
                    v___x_5349_,
                    v_t_5339_,
                );
                v_a_5352_ = crate::leanh::lean_ctor_get(v___x_5351_, 0);
                crate::leanh::lean_inc(v_a_5352_);
                crate::leanh::lean_dec(v___x_5351_);
                v___y_5342_ = v_a_5352_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_5343_ = crate::leanh::lean_ctor_get(v___y_5342_, 0);
                crate::leanh::lean_inc(v_fst_5343_);
                crate::leanh::lean_dec_ref(v___y_5342_);
                if crate::leanh::lean_obj_tag(v_fst_5343_) == 0 {
                    v___x_5344_ = 1;
                    return v___x_5344_;
                } else {
                    v_val_5345_ = crate::leanh::lean_ctor_get(v_fst_5343_, 0);
                    crate::leanh::lean_inc(v_val_5345_);
                    crate::leanh::lean_dec_ref_known(v_fst_5343_, 1);
                    v___x_5346_ = (crate::leanh::lean_unbox(v_val_5345_) as u8);
                    crate::leanh::lean_dec(v_val_5345_);
                    return v___x_5346_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(
    mut v_t_5353_: *mut crate::leanh::LeanObject,
    mut v_p_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5355_: u8 = 0;
    let mut v_r_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5355_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_5353_, v_p_5354_);
    v_r_5356_ = crate::leanh::lean_box((v_res_5355_) as usize);
    return v_r_5356_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all(
    mut v_00_u03b1_5357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5358_: *mut crate::leanh::LeanObject,
    mut v_t_5359_: *mut crate::leanh::LeanObject,
    mut v_p_5360_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: u8 = 0;
    let mut v_val_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5367_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
                v___x_5368_ = crate::leanh::lean_box(0);
                v___x_5369_ = l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0;
                v___f_5370_ = crate::leanh::lean_alloc_closure(
                    l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5370_, 0, v_p_5360_);
                crate::leanh::lean_closure_set(v___f_5370_, 1, v___x_5368_);
                crate::leanh::lean_closure_set(v___f_5370_, 2, v___x_5369_);
                v___x_5371_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
                    v___x_5367_,
                    v___f_5370_,
                    v___x_5369_,
                    v_t_5359_,
                );
                v_a_5372_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
                crate::leanh::lean_inc(v_a_5372_);
                crate::leanh::lean_dec(v___x_5371_);
                v___y_5362_ = v_a_5372_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_5363_ = crate::leanh::lean_ctor_get(v___y_5362_, 0);
                crate::leanh::lean_inc(v_fst_5363_);
                crate::leanh::lean_dec_ref(v___y_5362_);
                if crate::leanh::lean_obj_tag(v_fst_5363_) == 0 {
                    v___x_5364_ = 1;
                    return v___x_5364_;
                } else {
                    v_val_5365_ = crate::leanh::lean_ctor_get(v_fst_5363_, 0);
                    crate::leanh::lean_inc(v_val_5365_);
                    crate::leanh::lean_dec_ref_known(v_fst_5363_, 1);
                    v___x_5366_ = (crate::leanh::lean_unbox(v_val_5365_) as u8);
                    crate::leanh::lean_dec(v_val_5365_);
                    return v___x_5366_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_all___boxed(
    mut v_00_u03b1_5373_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5374_: *mut crate::leanh::LeanObject,
    mut v_t_5375_: *mut crate::leanh::LeanObject,
    mut v_p_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5377_: u8 = 0;
    let mut v_r_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5377_ =
        l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_5373_, v_00_u03b2_5374_, v_t_5375_, v_p_5376_);
    v_r_5378_ = crate::leanh::lean_box((v_res_5377_) as usize);
    return v_r_5378_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(
    mut v_x1_5379_: *mut crate::leanh::LeanObject,
    mut v_x2_5380_: *mut crate::leanh::LeanObject,
    mut v_x3_5381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5382_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5382_, 0, v_x1_5379_);
    crate::leanh::lean_ctor_set(v___x_5382_, 1, v_x3_5381_);
    return v___x_5382_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(
    mut v_x1_5383_: *mut crate::leanh::LeanObject,
    mut v_x2_5384_: *mut crate::leanh::LeanObject,
    mut v_x3_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5386_ =
        l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_5383_, v_x2_5384_, v_x3_5385_);
    crate::leanh::lean_dec(v_x2_5384_);
    return v_res_5386_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keys___redArg(
    mut v_t_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5389_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0;
    v___x_5390_ = crate::leanh::lean_box(0);
    v___x_5391_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5392_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5391_,
        v___f_5389_,
        v___x_5390_,
        v_t_5388_,
    );
    return v___x_5392_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keys(
    mut v_00_u03b1_5393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5394_: *mut crate::leanh::LeanObject,
    mut v_t_5395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5396_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0;
    v___x_5397_ = crate::leanh::lean_box(0);
    v___x_5398_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5399_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5398_,
        v___f_5396_,
        v___x_5397_,
        v_t_5395_,
    );
    return v___x_5399_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(
    mut v_l_5400_: *mut crate::leanh::LeanObject,
    mut v_k_5401_: *mut crate::leanh::LeanObject,
    mut v_x_5402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5403_ = lean_array_push(v_l_5400_, v_k_5401_);
    return v___x_5403_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(
    mut v_l_5404_: *mut crate::leanh::LeanObject,
    mut v_k_5405_: *mut crate::leanh::LeanObject,
    mut v_x_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5407_ =
        l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_5404_, v_k_5405_, v_x_5406_);
    crate::leanh::lean_dec(v_x_5406_);
    return v_res_5407_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keysArray___redArg(
    mut v_t_5409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5410_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5409_) == 0 {
                    v_size_5415_ = crate::leanh::lean_ctor_get(v_t_5409_, 0);
                    crate::leanh::lean_inc(v_size_5415_);
                    v___y_5412_ = v_size_5415_;
                    state = 1;
                    continue;
                } else {
                    v___x_5416_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5412_ = v___x_5416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5413_ = lean_mk_empty_array_with_capacity(v___y_5412_);
                crate::leanh::lean_dec(v___y_5412_);
                v___x_5414_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5410_,
                    v___x_5413_,
                    v_t_5409_,
                );
                return v___x_5414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keysArray(
    mut v_00_u03b1_5417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5418_: *mut crate::leanh::LeanObject,
    mut v_t_5419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5420_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5419_) == 0 {
                    v_size_5425_ = crate::leanh::lean_ctor_get(v_t_5419_, 0);
                    crate::leanh::lean_inc(v_size_5425_);
                    v___y_5422_ = v_size_5425_;
                    state = 1;
                    continue;
                } else {
                    v___x_5426_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5422_ = v___x_5426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5423_ = lean_mk_empty_array_with_capacity(v___y_5422_);
                crate::leanh::lean_dec(v___y_5422_);
                v___x_5424_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5420_,
                    v___x_5423_,
                    v_t_5419_,
                );
                return v___x_5424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(
    mut v_x1_5427_: *mut crate::leanh::LeanObject,
    mut v_x2_5428_: *mut crate::leanh::LeanObject,
    mut v_x3_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5430_, 0, v_x2_5428_);
    crate::leanh::lean_ctor_set(v___x_5430_, 1, v_x3_5429_);
    return v___x_5430_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(
    mut v_x1_5431_: *mut crate::leanh::LeanObject,
    mut v_x2_5432_: *mut crate::leanh::LeanObject,
    mut v_x3_5433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5434_ =
        l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_5431_, v_x2_5432_, v_x3_5433_);
    crate::leanh::lean_dec(v_x1_5431_);
    return v_res_5434_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_values___redArg(
    mut v_t_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5437_ = l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0;
    v___x_5438_ = crate::leanh::lean_box(0);
    v___x_5439_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5440_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5439_,
        v___f_5437_,
        v___x_5438_,
        v_t_5436_,
    );
    return v___x_5440_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_values(
    mut v_00_u03b1_5441_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5442_: *mut crate::leanh::LeanObject,
    mut v_t_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5444_ = l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0;
    v___x_5445_ = crate::leanh::lean_box(0);
    v___x_5446_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5447_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5446_,
        v___f_5444_,
        v___x_5445_,
        v_t_5443_,
    );
    return v___x_5447_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(
    mut v_l_5448_: *mut crate::leanh::LeanObject,
    mut v_x_5449_: *mut crate::leanh::LeanObject,
    mut v_v_5450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5451_ = lean_array_push(v_l_5448_, v_v_5450_);
    return v___x_5451_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(
    mut v_l_5452_: *mut crate::leanh::LeanObject,
    mut v_x_5453_: *mut crate::leanh::LeanObject,
    mut v_v_5454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5455_ =
        l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_5452_, v_x_5453_, v_v_5454_);
    crate::leanh::lean_dec(v_x_5453_);
    return v_res_5455_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(
    mut v_t_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5458_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5457_) == 0 {
                    v_size_5463_ = crate::leanh::lean_ctor_get(v_t_5457_, 0);
                    crate::leanh::lean_inc(v_size_5463_);
                    v___y_5460_ = v_size_5463_;
                    state = 1;
                    continue;
                } else {
                    v___x_5464_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5460_ = v___x_5464_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5461_ = lean_mk_empty_array_with_capacity(v___y_5460_);
                crate::leanh::lean_dec(v___y_5460_);
                v___x_5462_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5458_,
                    v___x_5461_,
                    v_t_5457_,
                );
                return v___x_5462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_valuesArray(
    mut v_00_u03b1_5465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5466_: *mut crate::leanh::LeanObject,
    mut v_t_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5468_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5467_) == 0 {
                    v_size_5473_ = crate::leanh::lean_ctor_get(v_t_5467_, 0);
                    crate::leanh::lean_inc(v_size_5473_);
                    v___y_5470_ = v_size_5473_;
                    state = 1;
                    continue;
                } else {
                    v___x_5474_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5470_ = v___x_5474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5471_ = lean_mk_empty_array_with_capacity(v___y_5470_);
                crate::leanh::lean_dec(v___y_5470_);
                v___x_5472_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5468_,
                    v___x_5471_,
                    v_t_5467_,
                );
                return v___x_5472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(
    mut v_x1_5475_: *mut crate::leanh::LeanObject,
    mut v_x2_5476_: *mut crate::leanh::LeanObject,
    mut v_x3_5477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5478_, 0, v_x1_5475_);
    crate::leanh::lean_ctor_set(v___x_5478_, 1, v_x2_5476_);
    v___x_5479_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5479_, 0, v___x_5478_);
    crate::leanh::lean_ctor_set(v___x_5479_, 1, v_x3_5477_);
    return v___x_5479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toList___redArg(
    mut v_t_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5482_ = l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0;
    v___x_5483_ = crate::leanh::lean_box(0);
    v___x_5484_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5485_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5484_,
        v___f_5482_,
        v___x_5483_,
        v_t_5481_,
    );
    return v___x_5485_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toList(
    mut v_00_u03b1_5486_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5487_: *mut crate::leanh::LeanObject,
    mut v_t_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5489_ = l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0;
    v___x_5490_ = crate::leanh::lean_box(0);
    v___x_5491_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5492_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5491_,
        v___f_5489_,
        v___x_5490_,
        v_t_5488_,
    );
    return v___x_5492_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(
    mut v_l_5493_: *mut crate::leanh::LeanObject,
    mut v_k_5494_: *mut crate::leanh::LeanObject,
    mut v_v_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5496_, 0, v_k_5494_);
    crate::leanh::lean_ctor_set(v___x_5496_, 1, v_v_5495_);
    v___x_5497_ = lean_array_push(v_l_5493_, v___x_5496_);
    return v___x_5497_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toArray___redArg(
    mut v_t_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5500_ = l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5499_) == 0 {
                    v_size_5505_ = crate::leanh::lean_ctor_get(v_t_5499_, 0);
                    crate::leanh::lean_inc(v_size_5505_);
                    v___y_5502_ = v_size_5505_;
                    state = 1;
                    continue;
                } else {
                    v___x_5506_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5502_ = v___x_5506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5503_ = lean_mk_empty_array_with_capacity(v___y_5502_);
                crate::leanh::lean_dec(v___y_5502_);
                v___x_5504_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5500_,
                    v___x_5503_,
                    v_t_5499_,
                );
                return v___x_5504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toArray(
    mut v_00_u03b1_5507_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5508_: *mut crate::leanh::LeanObject,
    mut v_t_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5510_ = l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5509_) == 0 {
                    v_size_5515_ = crate::leanh::lean_ctor_get(v_t_5509_, 0);
                    crate::leanh::lean_inc(v_size_5515_);
                    v___y_5512_ = v_size_5515_;
                    state = 1;
                    continue;
                } else {
                    v___x_5516_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5512_ = v___x_5516_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5513_ = lean_mk_empty_array_with_capacity(v___y_5512_);
                crate::leanh::lean_dec(v___y_5512_);
                v___x_5514_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5510_,
                    v___x_5513_,
                    v_t_5509_,
                );
                return v___x_5514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(
    mut v_x1_5517_: *mut crate::leanh::LeanObject,
    mut v_x2_5518_: *mut crate::leanh::LeanObject,
    mut v_x3_5519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5520_, 0, v_x1_5517_);
    crate::leanh::lean_ctor_set(v___x_5520_, 1, v_x2_5518_);
    v___x_5521_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5521_, 0, v___x_5520_);
    crate::leanh::lean_ctor_set(v___x_5521_, 1, v_x3_5519_);
    return v___x_5521_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(
    mut v_t_5523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5524_ = l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0;
    v___x_5525_ = crate::leanh::lean_box(0);
    v___x_5526_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5527_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5526_,
        v___f_5524_,
        v___x_5525_,
        v_t_5523_,
    );
    return v___x_5527_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toList(
    mut v_00_u03b1_5528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5529_: *mut crate::leanh::LeanObject,
    mut v_t_5530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5531_ = l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0;
    v___x_5532_ = crate::leanh::lean_box(0);
    v___x_5533_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9;
    v___x_5534_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_5533_,
        v___f_5531_,
        v___x_5532_,
        v_t_5530_,
    );
    return v___x_5534_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(
    mut v_l_5535_: *mut crate::leanh::LeanObject,
    mut v_k_5536_: *mut crate::leanh::LeanObject,
    mut v_v_5537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5538_, 0, v_k_5536_);
    crate::leanh::lean_ctor_set(v___x_5538_, 1, v_v_5537_);
    v___x_5539_ = lean_array_push(v_l_5535_, v___x_5538_);
    return v___x_5539_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(
    mut v_t_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5542_ = l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5541_) == 0 {
                    v_size_5547_ = crate::leanh::lean_ctor_get(v_t_5541_, 0);
                    crate::leanh::lean_inc(v_size_5547_);
                    v___y_5544_ = v_size_5547_;
                    state = 1;
                    continue;
                } else {
                    v___x_5548_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5544_ = v___x_5548_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5545_ = lean_mk_empty_array_with_capacity(v___y_5544_);
                crate::leanh::lean_dec(v___y_5544_);
                v___x_5546_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5542_,
                    v___x_5545_,
                    v_t_5541_,
                );
                return v___x_5546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_toArray(
    mut v_00_u03b1_5549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5550_: *mut crate::leanh::LeanObject,
    mut v_t_5551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5552_ = l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_5551_) == 0 {
                    v_size_5557_ = crate::leanh::lean_ctor_get(v_t_5551_, 0);
                    crate::leanh::lean_inc(v_size_5557_);
                    v___y_5554_ = v_size_5557_;
                    state = 1;
                    continue;
                } else {
                    v___x_5558_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5554_ = v___x_5558_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5555_ = lean_mk_empty_array_with_capacity(v___y_5554_);
                crate::leanh::lean_dec(v___y_5554_);
                v___x_5556_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_5552_,
                    v___x_5555_,
                    v_t_5551_,
                );
                return v___x_5556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(
    mut v_x_5559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5559_) == 0 {
                    v_l_5560_ = crate::leanh::lean_ctor_get(v_x_5559_, 3);
                    if crate::leanh::lean_obj_tag(v_l_5560_) == 0 {
                        v_x_5559_ = v_l_5560_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5562_ = crate::leanh::lean_ctor_get(v_x_5559_, 1);
                        v_v_5563_ = crate::leanh::lean_ctor_get(v_x_5559_, 2);
                        crate::leanh::lean_inc(v_v_5563_);
                        crate::leanh::lean_inc(v_k_5562_);
                        v___x_5564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5564_, 0, v_k_5562_);
                        crate::leanh::lean_ctor_set(v___x_5564_, 1, v_v_5563_);
                        v___x_5565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5565_, 0, v___x_5564_);
                        return v___x_5565_;
                    }
                } else {
                    v___x_5566_ = crate::leanh::lean_box(0);
                    return v___x_5566_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(
    mut v_x_5567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5568_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_5567_);
    crate::leanh::lean_dec(v_x_5567_);
    return v_res_5568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f(
    mut v_00_u03b1_5569_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5570_: *mut crate::leanh::LeanObject,
    mut v_x_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5572_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_5571_);
    return v___x_5572_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(
    mut v_00_u03b1_5573_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5574_: *mut crate::leanh::LeanObject,
    mut v_x_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5576_ =
        l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_5573_, v_00_u03b2_5574_, v_x_5575_);
    crate::leanh::lean_dec(v_x_5575_);
    return v_res_5576_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_5577_: *mut crate::leanh::LeanObject,
    mut v_h__1_5578_: *mut crate::leanh::LeanObject,
    mut v_h__2_5579_: *mut crate::leanh::LeanObject,
    mut v_h__3_5580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5577_) == 0 {
        let mut v_l_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5578_);
        v_l_5581_ = crate::leanh::lean_ctor_get(v_x_5577_, 3);
        if crate::leanh::lean_obj_tag(v_l_5581_) == 0 {
            let mut v_size_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_5581_);
            crate::leanh::lean_dec(v_h__2_5579_);
            v_size_5582_ = crate::leanh::lean_ctor_get(v_x_5577_, 0);
            crate::leanh::lean_inc(v_size_5582_);
            v_k_5583_ = crate::leanh::lean_ctor_get(v_x_5577_, 1);
            crate::leanh::lean_inc(v_k_5583_);
            v_v_5584_ = crate::leanh::lean_ctor_get(v_x_5577_, 2);
            crate::leanh::lean_inc(v_v_5584_);
            v_r_5585_ = crate::leanh::lean_ctor_get(v_x_5577_, 4);
            crate::leanh::lean_inc(v_r_5585_);
            crate::leanh::lean_dec_ref_known(v_x_5577_, 5);
            v_size_5586_ = crate::leanh::lean_ctor_get(v_l_5581_, 0);
            crate::leanh::lean_inc(v_size_5586_);
            v_k_5587_ = crate::leanh::lean_ctor_get(v_l_5581_, 1);
            crate::leanh::lean_inc(v_k_5587_);
            v_v_5588_ = crate::leanh::lean_ctor_get(v_l_5581_, 2);
            crate::leanh::lean_inc(v_v_5588_);
            v_l_5589_ = crate::leanh::lean_ctor_get(v_l_5581_, 3);
            crate::leanh::lean_inc(v_l_5589_);
            v_r_5590_ = crate::leanh::lean_ctor_get(v_l_5581_, 4);
            crate::leanh::lean_inc(v_r_5590_);
            crate::leanh::lean_dec_ref_known(v_l_5581_, 5);
            v___x_5591_ = crate::leanh::lean_apply_9(
                v_h__3_5580_,
                v_size_5582_,
                v_k_5583_,
                v_v_5584_,
                v_size_5586_,
                v_k_5587_,
                v_v_5588_,
                v_l_5589_,
                v_r_5590_,
                v_r_5585_,
            );
            return v___x_5591_;
        } else {
            let mut v_size_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5580_);
            v_size_5592_ = crate::leanh::lean_ctor_get(v_x_5577_, 0);
            crate::leanh::lean_inc(v_size_5592_);
            v_k_5593_ = crate::leanh::lean_ctor_get(v_x_5577_, 1);
            crate::leanh::lean_inc(v_k_5593_);
            v_v_5594_ = crate::leanh::lean_ctor_get(v_x_5577_, 2);
            crate::leanh::lean_inc(v_v_5594_);
            v_r_5595_ = crate::leanh::lean_ctor_get(v_x_5577_, 4);
            crate::leanh::lean_inc(v_r_5595_);
            crate::leanh::lean_dec_ref_known(v_x_5577_, 5);
            v___x_5596_ = crate::leanh::lean_apply_4(
                v_h__2_5579_,
                v_size_5592_,
                v_k_5593_,
                v_v_5594_,
                v_r_5595_,
            );
            return v___x_5596_;
        }
    } else {
        let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5580_);
        crate::leanh::lean_dec(v_h__2_5579_);
        v___x_5597_ = crate::leanh::lean_box(0);
        v___x_5598_ = crate::leanh::lean_apply_1(v_h__1_5578_, v___x_5597_);
        return v___x_5598_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_5599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5600_: *mut crate::leanh::LeanObject,
    mut v_motive_5601_: *mut crate::leanh::LeanObject,
    mut v_x_5602_: *mut crate::leanh::LeanObject,
    mut v_h__1_5603_: *mut crate::leanh::LeanObject,
    mut v_h__2_5604_: *mut crate::leanh::LeanObject,
    mut v_h__3_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5602_) == 0 {
        let mut v_l_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5603_);
        v_l_5606_ = crate::leanh::lean_ctor_get(v_x_5602_, 3);
        if crate::leanh::lean_obj_tag(v_l_5606_) == 0 {
            let mut v_size_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_5606_);
            crate::leanh::lean_dec(v_h__2_5604_);
            v_size_5607_ = crate::leanh::lean_ctor_get(v_x_5602_, 0);
            crate::leanh::lean_inc(v_size_5607_);
            v_k_5608_ = crate::leanh::lean_ctor_get(v_x_5602_, 1);
            crate::leanh::lean_inc(v_k_5608_);
            v_v_5609_ = crate::leanh::lean_ctor_get(v_x_5602_, 2);
            crate::leanh::lean_inc(v_v_5609_);
            v_r_5610_ = crate::leanh::lean_ctor_get(v_x_5602_, 4);
            crate::leanh::lean_inc(v_r_5610_);
            crate::leanh::lean_dec_ref_known(v_x_5602_, 5);
            v_size_5611_ = crate::leanh::lean_ctor_get(v_l_5606_, 0);
            crate::leanh::lean_inc(v_size_5611_);
            v_k_5612_ = crate::leanh::lean_ctor_get(v_l_5606_, 1);
            crate::leanh::lean_inc(v_k_5612_);
            v_v_5613_ = crate::leanh::lean_ctor_get(v_l_5606_, 2);
            crate::leanh::lean_inc(v_v_5613_);
            v_l_5614_ = crate::leanh::lean_ctor_get(v_l_5606_, 3);
            crate::leanh::lean_inc(v_l_5614_);
            v_r_5615_ = crate::leanh::lean_ctor_get(v_l_5606_, 4);
            crate::leanh::lean_inc(v_r_5615_);
            crate::leanh::lean_dec_ref_known(v_l_5606_, 5);
            v___x_5616_ = crate::leanh::lean_apply_9(
                v_h__3_5605_,
                v_size_5607_,
                v_k_5608_,
                v_v_5609_,
                v_size_5611_,
                v_k_5612_,
                v_v_5613_,
                v_l_5614_,
                v_r_5615_,
                v_r_5610_,
            );
            return v___x_5616_;
        } else {
            let mut v_size_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5605_);
            v_size_5617_ = crate::leanh::lean_ctor_get(v_x_5602_, 0);
            crate::leanh::lean_inc(v_size_5617_);
            v_k_5618_ = crate::leanh::lean_ctor_get(v_x_5602_, 1);
            crate::leanh::lean_inc(v_k_5618_);
            v_v_5619_ = crate::leanh::lean_ctor_get(v_x_5602_, 2);
            crate::leanh::lean_inc(v_v_5619_);
            v_r_5620_ = crate::leanh::lean_ctor_get(v_x_5602_, 4);
            crate::leanh::lean_inc(v_r_5620_);
            crate::leanh::lean_dec_ref_known(v_x_5602_, 5);
            v___x_5621_ = crate::leanh::lean_apply_4(
                v_h__2_5604_,
                v_size_5617_,
                v_k_5618_,
                v_v_5619_,
                v_r_5620_,
            );
            return v___x_5621_;
        }
    } else {
        let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5605_);
        crate::leanh::lean_dec(v_h__2_5604_);
        v___x_5622_ = crate::leanh::lean_box(0);
        v___x_5623_ = crate::leanh::lean_apply_1(v_h__1_5603_, v___x_5622_);
        return v___x_5623_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry___redArg(
    mut v_x_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_l_5625_ = crate::leanh::lean_ctor_get(v_x_5624_, 3);
                if crate::leanh::lean_obj_tag(v_l_5625_) == 0 {
                    v_x_5624_ = v_l_5625_;
                    state = 0;
                    continue;
                } else {
                    v_k_5627_ = crate::leanh::lean_ctor_get(v_x_5624_, 1);
                    v_v_5628_ = crate::leanh::lean_ctor_get(v_x_5624_, 2);
                    crate::leanh::lean_inc(v_v_5628_);
                    crate::leanh::lean_inc(v_k_5627_);
                    v___x_5629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5629_, 0, v_k_5627_);
                    crate::leanh::lean_ctor_set(v___x_5629_, 1, v_v_5628_);
                    return v___x_5629_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(
    mut v_x_5630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5631_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_5630_);
    crate::leanh::lean_dec(v_x_5630_);
    return v_res_5631_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry(
    mut v_00_u03b1_5632_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5633_: *mut crate::leanh::LeanObject,
    mut v_x_5634_: *mut crate::leanh::LeanObject,
    mut v_x_5635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_5634_);
    return v___x_5636_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry___boxed(
    mut v_00_u03b1_5637_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5638_: *mut crate::leanh::LeanObject,
    mut v_x_5639_: *mut crate::leanh::LeanObject,
    mut v_x_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5641_ = l_Std_DTreeMap_Internal_Impl_minEntry(
        v_00_u03b1_5637_,
        v_00_u03b2_5638_,
        v_x_5639_,
        v_x_5640_,
    );
    crate::leanh::lean_dec(v_x_5639_);
    return v_res_5641_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(
    mut v_x_5642_: *mut crate::leanh::LeanObject,
    mut v_h__1_5643_: *mut crate::leanh::LeanObject,
    mut v_h__2_5644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_5645_ = crate::leanh::lean_ctor_get(v_x_5642_, 3);
    if crate::leanh::lean_obj_tag(v_l_5645_) == 0 {
        let mut v_size_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_5645_);
        crate::leanh::lean_dec(v_h__1_5643_);
        v_size_5646_ = crate::leanh::lean_ctor_get(v_x_5642_, 0);
        crate::leanh::lean_inc(v_size_5646_);
        v_k_5647_ = crate::leanh::lean_ctor_get(v_x_5642_, 1);
        crate::leanh::lean_inc(v_k_5647_);
        v_v_5648_ = crate::leanh::lean_ctor_get(v_x_5642_, 2);
        crate::leanh::lean_inc(v_v_5648_);
        v_r_5649_ = crate::leanh::lean_ctor_get(v_x_5642_, 4);
        crate::leanh::lean_inc(v_r_5649_);
        crate::leanh::lean_dec(v_x_5642_);
        v_size_5650_ = crate::leanh::lean_ctor_get(v_l_5645_, 0);
        crate::leanh::lean_inc(v_size_5650_);
        v_k_5651_ = crate::leanh::lean_ctor_get(v_l_5645_, 1);
        crate::leanh::lean_inc(v_k_5651_);
        v_v_5652_ = crate::leanh::lean_ctor_get(v_l_5645_, 2);
        crate::leanh::lean_inc(v_v_5652_);
        v_l_5653_ = crate::leanh::lean_ctor_get(v_l_5645_, 3);
        crate::leanh::lean_inc(v_l_5653_);
        v_r_5654_ = crate::leanh::lean_ctor_get(v_l_5645_, 4);
        crate::leanh::lean_inc(v_r_5654_);
        crate::leanh::lean_dec_ref_known(v_l_5645_, 5);
        v___x_5655_ = crate::leanh::lean_apply_10(
            v_h__2_5644_,
            v_size_5646_,
            v_k_5647_,
            v_v_5648_,
            v_size_5650_,
            v_k_5651_,
            v_v_5652_,
            v_l_5653_,
            v_r_5654_,
            v_r_5649_,
            crate::leanh::lean_box(0),
        );
        return v___x_5655_;
    } else {
        let mut v_size_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5644_);
        v_size_5656_ = crate::leanh::lean_ctor_get(v_x_5642_, 0);
        crate::leanh::lean_inc(v_size_5656_);
        v_k_5657_ = crate::leanh::lean_ctor_get(v_x_5642_, 1);
        crate::leanh::lean_inc(v_k_5657_);
        v_v_5658_ = crate::leanh::lean_ctor_get(v_x_5642_, 2);
        crate::leanh::lean_inc(v_v_5658_);
        v_r_5659_ = crate::leanh::lean_ctor_get(v_x_5642_, 4);
        crate::leanh::lean_inc(v_r_5659_);
        crate::leanh::lean_dec(v_x_5642_);
        v___x_5660_ = crate::leanh::lean_apply_5(
            v_h__1_5643_,
            v_size_5656_,
            v_k_5657_,
            v_v_5658_,
            v_r_5659_,
            crate::leanh::lean_box(0),
        );
        return v___x_5660_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(
    mut v_00_u03b1_5661_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5662_: *mut crate::leanh::LeanObject,
    mut v_motive_5663_: *mut crate::leanh::LeanObject,
    mut v_x_5664_: *mut crate::leanh::LeanObject,
    mut v_x_5665_: *mut crate::leanh::LeanObject,
    mut v_h__1_5666_: *mut crate::leanh::LeanObject,
    mut v_h__2_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_5668_ = crate::leanh::lean_ctor_get(v_x_5664_, 3);
    if crate::leanh::lean_obj_tag(v_l_5668_) == 0 {
        let mut v_size_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_5668_);
        crate::leanh::lean_dec(v_h__1_5666_);
        v_size_5669_ = crate::leanh::lean_ctor_get(v_x_5664_, 0);
        crate::leanh::lean_inc(v_size_5669_);
        v_k_5670_ = crate::leanh::lean_ctor_get(v_x_5664_, 1);
        crate::leanh::lean_inc(v_k_5670_);
        v_v_5671_ = crate::leanh::lean_ctor_get(v_x_5664_, 2);
        crate::leanh::lean_inc(v_v_5671_);
        v_r_5672_ = crate::leanh::lean_ctor_get(v_x_5664_, 4);
        crate::leanh::lean_inc(v_r_5672_);
        crate::leanh::lean_dec(v_x_5664_);
        v_size_5673_ = crate::leanh::lean_ctor_get(v_l_5668_, 0);
        crate::leanh::lean_inc(v_size_5673_);
        v_k_5674_ = crate::leanh::lean_ctor_get(v_l_5668_, 1);
        crate::leanh::lean_inc(v_k_5674_);
        v_v_5675_ = crate::leanh::lean_ctor_get(v_l_5668_, 2);
        crate::leanh::lean_inc(v_v_5675_);
        v_l_5676_ = crate::leanh::lean_ctor_get(v_l_5668_, 3);
        crate::leanh::lean_inc(v_l_5676_);
        v_r_5677_ = crate::leanh::lean_ctor_get(v_l_5668_, 4);
        crate::leanh::lean_inc(v_r_5677_);
        crate::leanh::lean_dec_ref_known(v_l_5668_, 5);
        v___x_5678_ = crate::leanh::lean_apply_10(
            v_h__2_5667_,
            v_size_5669_,
            v_k_5670_,
            v_v_5671_,
            v_size_5673_,
            v_k_5674_,
            v_v_5675_,
            v_l_5676_,
            v_r_5677_,
            v_r_5672_,
            crate::leanh::lean_box(0),
        );
        return v___x_5678_;
    } else {
        let mut v_size_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5667_);
        v_size_5679_ = crate::leanh::lean_ctor_get(v_x_5664_, 0);
        crate::leanh::lean_inc(v_size_5679_);
        v_k_5680_ = crate::leanh::lean_ctor_get(v_x_5664_, 1);
        crate::leanh::lean_inc(v_k_5680_);
        v_v_5681_ = crate::leanh::lean_ctor_get(v_x_5664_, 2);
        crate::leanh::lean_inc(v_v_5681_);
        v_r_5682_ = crate::leanh::lean_ctor_get(v_x_5664_, 4);
        crate::leanh::lean_inc(v_r_5682_);
        crate::leanh::lean_dec(v_x_5664_);
        v___x_5683_ = crate::leanh::lean_apply_5(
            v_h__1_5666_,
            v_size_5679_,
            v_k_5680_,
            v_v_5681_,
            v_r_5682_,
            crate::leanh::lean_box(0),
        );
        return v___x_5683_;
    }
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_5687_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_5688_ = crate::leanh::lean_unsigned_to_nat(367);
    v___x_5689_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0;
    v___x_5690_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_5691_ = l_mkPanicMessageWithDecl(
        v___x_5690_,
        v___x_5689_,
        v___x_5688_,
        v___x_5687_,
        v___x_5686_,
    );
    return v___x_5691_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(
    mut v_inst_5692_: *mut crate::leanh::LeanObject,
    mut v_x_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5693_) == 0 {
                    v_l_5694_ = crate::leanh::lean_ctor_get(v_x_5693_, 3);
                    if crate::leanh::lean_obj_tag(v_l_5694_) == 0 {
                        v_x_5693_ = v_l_5694_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5696_ = crate::leanh::lean_ctor_get(v_x_5693_, 1);
                        v_v_5697_ = crate::leanh::lean_ctor_get(v_x_5693_, 2);
                        crate::leanh::lean_inc(v_v_5697_);
                        crate::leanh::lean_inc(v_k_5696_);
                        v___x_5698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5698_, 0, v_k_5696_);
                        crate::leanh::lean_ctor_set(v___x_5698_, 1, v_v_5697_);
                        return v___x_5698_;
                    }
                } else {
                    v___x_5699_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2,
                    );
                    v___x_5700_ = l_panic___redArg(v_inst_5692_, v___x_5699_);
                    return v___x_5700_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(
    mut v_inst_5701_: *mut crate::leanh::LeanObject,
    mut v_x_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5703_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_5701_, v_x_5702_);
    crate::leanh::lean_dec(v_x_5702_);
    crate::leanh::lean_dec_ref(v_inst_5701_);
    return v_res_5703_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x21(
    mut v_00_u03b1_5704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5705_: *mut crate::leanh::LeanObject,
    mut v_inst_5706_: *mut crate::leanh::LeanObject,
    mut v_x_5707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5708_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_5706_, v_x_5707_);
    return v___x_5708_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(
    mut v_00_u03b1_5709_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5710_: *mut crate::leanh::LeanObject,
    mut v_inst_5711_: *mut crate::leanh::LeanObject,
    mut v_x_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5713_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(
        v_00_u03b1_5709_,
        v_00_u03b2_5710_,
        v_inst_5711_,
        v_x_5712_,
    );
    crate::leanh::lean_dec(v_x_5712_);
    crate::leanh::lean_dec_ref(v_inst_5711_);
    return v_res_5713_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(
    mut v_x_5714_: *mut crate::leanh::LeanObject,
    mut v_x_5715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5714_) == 0 {
                    v_l_5716_ = crate::leanh::lean_ctor_get(v_x_5714_, 3);
                    if crate::leanh::lean_obj_tag(v_l_5716_) == 0 {
                        v_x_5714_ = v_l_5716_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5718_ = crate::leanh::lean_ctor_get(v_x_5714_, 1);
                        v_v_5719_ = crate::leanh::lean_ctor_get(v_x_5714_, 2);
                        crate::leanh::lean_inc(v_v_5719_);
                        crate::leanh::lean_inc(v_k_5718_);
                        v___x_5720_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5720_, 0, v_k_5718_);
                        crate::leanh::lean_ctor_set(v___x_5720_, 1, v_v_5719_);
                        return v___x_5720_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_x_5715_);
                    return v_x_5715_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(
    mut v_x_5721_: *mut crate::leanh::LeanObject,
    mut v_x_5722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5723_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_5721_, v_x_5722_);
    crate::leanh::lean_dec_ref(v_x_5722_);
    crate::leanh::lean_dec(v_x_5721_);
    return v_res_5723_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntryD(
    mut v_00_u03b1_5724_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5725_: *mut crate::leanh::LeanObject,
    mut v_x_5726_: *mut crate::leanh::LeanObject,
    mut v_x_5727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5728_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_5726_, v_x_5727_);
    return v___x_5728_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(
    mut v_00_u03b1_5729_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5730_: *mut crate::leanh::LeanObject,
    mut v_x_5731_: *mut crate::leanh::LeanObject,
    mut v_x_5732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5733_ = l_Std_DTreeMap_Internal_Impl_minEntryD(
        v_00_u03b1_5729_,
        v_00_u03b2_5730_,
        v_x_5731_,
        v_x_5732_,
    );
    crate::leanh::lean_dec_ref(v_x_5732_);
    crate::leanh::lean_dec(v_x_5731_);
    return v_res_5733_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(
    mut v_x_5734_: *mut crate::leanh::LeanObject,
    mut v_x_5735_: *mut crate::leanh::LeanObject,
    mut v_h__1_5736_: *mut crate::leanh::LeanObject,
    mut v_h__2_5737_: *mut crate::leanh::LeanObject,
    mut v_h__3_5738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5734_) == 0 {
        let mut v_l_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5736_);
        v_l_5739_ = crate::leanh::lean_ctor_get(v_x_5734_, 3);
        if crate::leanh::lean_obj_tag(v_l_5739_) == 0 {
            let mut v_size_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_5739_);
            crate::leanh::lean_dec(v_h__2_5737_);
            v_size_5740_ = crate::leanh::lean_ctor_get(v_x_5734_, 0);
            crate::leanh::lean_inc(v_size_5740_);
            v_k_5741_ = crate::leanh::lean_ctor_get(v_x_5734_, 1);
            crate::leanh::lean_inc(v_k_5741_);
            v_v_5742_ = crate::leanh::lean_ctor_get(v_x_5734_, 2);
            crate::leanh::lean_inc(v_v_5742_);
            v_r_5743_ = crate::leanh::lean_ctor_get(v_x_5734_, 4);
            crate::leanh::lean_inc(v_r_5743_);
            crate::leanh::lean_dec_ref_known(v_x_5734_, 5);
            v_size_5744_ = crate::leanh::lean_ctor_get(v_l_5739_, 0);
            crate::leanh::lean_inc(v_size_5744_);
            v_k_5745_ = crate::leanh::lean_ctor_get(v_l_5739_, 1);
            crate::leanh::lean_inc(v_k_5745_);
            v_v_5746_ = crate::leanh::lean_ctor_get(v_l_5739_, 2);
            crate::leanh::lean_inc(v_v_5746_);
            v_l_5747_ = crate::leanh::lean_ctor_get(v_l_5739_, 3);
            crate::leanh::lean_inc(v_l_5747_);
            v_r_5748_ = crate::leanh::lean_ctor_get(v_l_5739_, 4);
            crate::leanh::lean_inc(v_r_5748_);
            crate::leanh::lean_dec_ref_known(v_l_5739_, 5);
            v___x_5749_ = crate::leanh::lean_apply_10(
                v_h__3_5738_,
                v_size_5740_,
                v_k_5741_,
                v_v_5742_,
                v_size_5744_,
                v_k_5745_,
                v_v_5746_,
                v_l_5747_,
                v_r_5748_,
                v_r_5743_,
                v_x_5735_,
            );
            return v___x_5749_;
        } else {
            let mut v_size_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5738_);
            v_size_5750_ = crate::leanh::lean_ctor_get(v_x_5734_, 0);
            crate::leanh::lean_inc(v_size_5750_);
            v_k_5751_ = crate::leanh::lean_ctor_get(v_x_5734_, 1);
            crate::leanh::lean_inc(v_k_5751_);
            v_v_5752_ = crate::leanh::lean_ctor_get(v_x_5734_, 2);
            crate::leanh::lean_inc(v_v_5752_);
            v_r_5753_ = crate::leanh::lean_ctor_get(v_x_5734_, 4);
            crate::leanh::lean_inc(v_r_5753_);
            crate::leanh::lean_dec_ref_known(v_x_5734_, 5);
            v___x_5754_ = crate::leanh::lean_apply_5(
                v_h__2_5737_,
                v_size_5750_,
                v_k_5751_,
                v_v_5752_,
                v_r_5753_,
                v_x_5735_,
            );
            return v___x_5754_;
        }
    } else {
        let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5738_);
        crate::leanh::lean_dec(v_h__2_5737_);
        v___x_5755_ = crate::leanh::lean_apply_1(v_h__1_5736_, v_x_5735_);
        return v___x_5755_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(
    mut v_00_u03b1_5756_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5757_: *mut crate::leanh::LeanObject,
    mut v_motive_5758_: *mut crate::leanh::LeanObject,
    mut v_x_5759_: *mut crate::leanh::LeanObject,
    mut v_x_5760_: *mut crate::leanh::LeanObject,
    mut v_h__1_5761_: *mut crate::leanh::LeanObject,
    mut v_h__2_5762_: *mut crate::leanh::LeanObject,
    mut v_h__3_5763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5759_) == 0 {
        let mut v_l_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5761_);
        v_l_5764_ = crate::leanh::lean_ctor_get(v_x_5759_, 3);
        if crate::leanh::lean_obj_tag(v_l_5764_) == 0 {
            let mut v_size_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_5764_);
            crate::leanh::lean_dec(v_h__2_5762_);
            v_size_5765_ = crate::leanh::lean_ctor_get(v_x_5759_, 0);
            crate::leanh::lean_inc(v_size_5765_);
            v_k_5766_ = crate::leanh::lean_ctor_get(v_x_5759_, 1);
            crate::leanh::lean_inc(v_k_5766_);
            v_v_5767_ = crate::leanh::lean_ctor_get(v_x_5759_, 2);
            crate::leanh::lean_inc(v_v_5767_);
            v_r_5768_ = crate::leanh::lean_ctor_get(v_x_5759_, 4);
            crate::leanh::lean_inc(v_r_5768_);
            crate::leanh::lean_dec_ref_known(v_x_5759_, 5);
            v_size_5769_ = crate::leanh::lean_ctor_get(v_l_5764_, 0);
            crate::leanh::lean_inc(v_size_5769_);
            v_k_5770_ = crate::leanh::lean_ctor_get(v_l_5764_, 1);
            crate::leanh::lean_inc(v_k_5770_);
            v_v_5771_ = crate::leanh::lean_ctor_get(v_l_5764_, 2);
            crate::leanh::lean_inc(v_v_5771_);
            v_l_5772_ = crate::leanh::lean_ctor_get(v_l_5764_, 3);
            crate::leanh::lean_inc(v_l_5772_);
            v_r_5773_ = crate::leanh::lean_ctor_get(v_l_5764_, 4);
            crate::leanh::lean_inc(v_r_5773_);
            crate::leanh::lean_dec_ref_known(v_l_5764_, 5);
            v___x_5774_ = crate::leanh::lean_apply_10(
                v_h__3_5763_,
                v_size_5765_,
                v_k_5766_,
                v_v_5767_,
                v_size_5769_,
                v_k_5770_,
                v_v_5771_,
                v_l_5772_,
                v_r_5773_,
                v_r_5768_,
                v_x_5760_,
            );
            return v___x_5774_;
        } else {
            let mut v_size_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5763_);
            v_size_5775_ = crate::leanh::lean_ctor_get(v_x_5759_, 0);
            crate::leanh::lean_inc(v_size_5775_);
            v_k_5776_ = crate::leanh::lean_ctor_get(v_x_5759_, 1);
            crate::leanh::lean_inc(v_k_5776_);
            v_v_5777_ = crate::leanh::lean_ctor_get(v_x_5759_, 2);
            crate::leanh::lean_inc(v_v_5777_);
            v_r_5778_ = crate::leanh::lean_ctor_get(v_x_5759_, 4);
            crate::leanh::lean_inc(v_r_5778_);
            crate::leanh::lean_dec_ref_known(v_x_5759_, 5);
            v___x_5779_ = crate::leanh::lean_apply_5(
                v_h__2_5762_,
                v_size_5775_,
                v_k_5776_,
                v_v_5777_,
                v_r_5778_,
                v_x_5760_,
            );
            return v___x_5779_;
        }
    } else {
        let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5763_);
        crate::leanh::lean_dec(v_h__2_5762_);
        v___x_5780_ = crate::leanh::lean_apply_1(v_h__1_5761_, v_x_5760_);
        return v___x_5780_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(
    mut v_x_5781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5781_) == 0 {
                    v_r_5782_ = crate::leanh::lean_ctor_get(v_x_5781_, 4);
                    if crate::leanh::lean_obj_tag(v_r_5782_) == 0 {
                        v_x_5781_ = v_r_5782_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5784_ = crate::leanh::lean_ctor_get(v_x_5781_, 1);
                        v_v_5785_ = crate::leanh::lean_ctor_get(v_x_5781_, 2);
                        crate::leanh::lean_inc(v_v_5785_);
                        crate::leanh::lean_inc(v_k_5784_);
                        v___x_5786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5786_, 0, v_k_5784_);
                        crate::leanh::lean_ctor_set(v___x_5786_, 1, v_v_5785_);
                        v___x_5787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5787_, 0, v___x_5786_);
                        return v___x_5787_;
                    }
                } else {
                    v___x_5788_ = crate::leanh::lean_box(0);
                    return v___x_5788_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(
    mut v_x_5789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_5789_);
    crate::leanh::lean_dec(v_x_5789_);
    return v_res_5790_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(
    mut v_00_u03b1_5791_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5792_: *mut crate::leanh::LeanObject,
    mut v_x_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5794_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_5793_);
    return v___x_5794_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(
    mut v_00_u03b1_5795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5796_: *mut crate::leanh::LeanObject,
    mut v_x_5797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5798_ =
        l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_5795_, v_00_u03b2_5796_, v_x_5797_);
    crate::leanh::lean_dec(v_x_5797_);
    return v_res_5798_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_5799_: *mut crate::leanh::LeanObject,
    mut v_h__1_5800_: *mut crate::leanh::LeanObject,
    mut v_h__2_5801_: *mut crate::leanh::LeanObject,
    mut v_h__3_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5799_) == 0 {
        let mut v_r_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5800_);
        v_r_5803_ = crate::leanh::lean_ctor_get(v_x_5799_, 4);
        if crate::leanh::lean_obj_tag(v_r_5803_) == 0 {
            let mut v_size_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_5803_);
            crate::leanh::lean_dec(v_h__2_5801_);
            v_size_5804_ = crate::leanh::lean_ctor_get(v_x_5799_, 0);
            crate::leanh::lean_inc(v_size_5804_);
            v_k_5805_ = crate::leanh::lean_ctor_get(v_x_5799_, 1);
            crate::leanh::lean_inc(v_k_5805_);
            v_v_5806_ = crate::leanh::lean_ctor_get(v_x_5799_, 2);
            crate::leanh::lean_inc(v_v_5806_);
            v_l_5807_ = crate::leanh::lean_ctor_get(v_x_5799_, 3);
            crate::leanh::lean_inc(v_l_5807_);
            crate::leanh::lean_dec_ref_known(v_x_5799_, 5);
            v_size_5808_ = crate::leanh::lean_ctor_get(v_r_5803_, 0);
            crate::leanh::lean_inc(v_size_5808_);
            v_k_5809_ = crate::leanh::lean_ctor_get(v_r_5803_, 1);
            crate::leanh::lean_inc(v_k_5809_);
            v_v_5810_ = crate::leanh::lean_ctor_get(v_r_5803_, 2);
            crate::leanh::lean_inc(v_v_5810_);
            v_l_5811_ = crate::leanh::lean_ctor_get(v_r_5803_, 3);
            crate::leanh::lean_inc(v_l_5811_);
            v_r_5812_ = crate::leanh::lean_ctor_get(v_r_5803_, 4);
            crate::leanh::lean_inc(v_r_5812_);
            crate::leanh::lean_dec_ref_known(v_r_5803_, 5);
            v___x_5813_ = crate::leanh::lean_apply_9(
                v_h__3_5802_,
                v_size_5804_,
                v_k_5805_,
                v_v_5806_,
                v_l_5807_,
                v_size_5808_,
                v_k_5809_,
                v_v_5810_,
                v_l_5811_,
                v_r_5812_,
            );
            return v___x_5813_;
        } else {
            let mut v_size_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5802_);
            v_size_5814_ = crate::leanh::lean_ctor_get(v_x_5799_, 0);
            crate::leanh::lean_inc(v_size_5814_);
            v_k_5815_ = crate::leanh::lean_ctor_get(v_x_5799_, 1);
            crate::leanh::lean_inc(v_k_5815_);
            v_v_5816_ = crate::leanh::lean_ctor_get(v_x_5799_, 2);
            crate::leanh::lean_inc(v_v_5816_);
            v_l_5817_ = crate::leanh::lean_ctor_get(v_x_5799_, 3);
            crate::leanh::lean_inc(v_l_5817_);
            crate::leanh::lean_dec_ref_known(v_x_5799_, 5);
            v___x_5818_ = crate::leanh::lean_apply_4(
                v_h__2_5801_,
                v_size_5814_,
                v_k_5815_,
                v_v_5816_,
                v_l_5817_,
            );
            return v___x_5818_;
        }
    } else {
        let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5802_);
        crate::leanh::lean_dec(v_h__2_5801_);
        v___x_5819_ = crate::leanh::lean_box(0);
        v___x_5820_ = crate::leanh::lean_apply_1(v_h__1_5800_, v___x_5819_);
        return v___x_5820_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_5821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5822_: *mut crate::leanh::LeanObject,
    mut v_motive_5823_: *mut crate::leanh::LeanObject,
    mut v_x_5824_: *mut crate::leanh::LeanObject,
    mut v_h__1_5825_: *mut crate::leanh::LeanObject,
    mut v_h__2_5826_: *mut crate::leanh::LeanObject,
    mut v_h__3_5827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5824_) == 0 {
        let mut v_r_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5825_);
        v_r_5828_ = crate::leanh::lean_ctor_get(v_x_5824_, 4);
        if crate::leanh::lean_obj_tag(v_r_5828_) == 0 {
            let mut v_size_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_5828_);
            crate::leanh::lean_dec(v_h__2_5826_);
            v_size_5829_ = crate::leanh::lean_ctor_get(v_x_5824_, 0);
            crate::leanh::lean_inc(v_size_5829_);
            v_k_5830_ = crate::leanh::lean_ctor_get(v_x_5824_, 1);
            crate::leanh::lean_inc(v_k_5830_);
            v_v_5831_ = crate::leanh::lean_ctor_get(v_x_5824_, 2);
            crate::leanh::lean_inc(v_v_5831_);
            v_l_5832_ = crate::leanh::lean_ctor_get(v_x_5824_, 3);
            crate::leanh::lean_inc(v_l_5832_);
            crate::leanh::lean_dec_ref_known(v_x_5824_, 5);
            v_size_5833_ = crate::leanh::lean_ctor_get(v_r_5828_, 0);
            crate::leanh::lean_inc(v_size_5833_);
            v_k_5834_ = crate::leanh::lean_ctor_get(v_r_5828_, 1);
            crate::leanh::lean_inc(v_k_5834_);
            v_v_5835_ = crate::leanh::lean_ctor_get(v_r_5828_, 2);
            crate::leanh::lean_inc(v_v_5835_);
            v_l_5836_ = crate::leanh::lean_ctor_get(v_r_5828_, 3);
            crate::leanh::lean_inc(v_l_5836_);
            v_r_5837_ = crate::leanh::lean_ctor_get(v_r_5828_, 4);
            crate::leanh::lean_inc(v_r_5837_);
            crate::leanh::lean_dec_ref_known(v_r_5828_, 5);
            v___x_5838_ = crate::leanh::lean_apply_9(
                v_h__3_5827_,
                v_size_5829_,
                v_k_5830_,
                v_v_5831_,
                v_l_5832_,
                v_size_5833_,
                v_k_5834_,
                v_v_5835_,
                v_l_5836_,
                v_r_5837_,
            );
            return v___x_5838_;
        } else {
            let mut v_size_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5827_);
            v_size_5839_ = crate::leanh::lean_ctor_get(v_x_5824_, 0);
            crate::leanh::lean_inc(v_size_5839_);
            v_k_5840_ = crate::leanh::lean_ctor_get(v_x_5824_, 1);
            crate::leanh::lean_inc(v_k_5840_);
            v_v_5841_ = crate::leanh::lean_ctor_get(v_x_5824_, 2);
            crate::leanh::lean_inc(v_v_5841_);
            v_l_5842_ = crate::leanh::lean_ctor_get(v_x_5824_, 3);
            crate::leanh::lean_inc(v_l_5842_);
            crate::leanh::lean_dec_ref_known(v_x_5824_, 5);
            v___x_5843_ = crate::leanh::lean_apply_4(
                v_h__2_5826_,
                v_size_5839_,
                v_k_5840_,
                v_v_5841_,
                v_l_5842_,
            );
            return v___x_5843_;
        }
    } else {
        let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5827_);
        crate::leanh::lean_dec(v_h__2_5826_);
        v___x_5844_ = crate::leanh::lean_box(0);
        v___x_5845_ = crate::leanh::lean_apply_1(v_h__1_5825_, v___x_5844_);
        return v___x_5845_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(
    mut v_x_5846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_5847_ = crate::leanh::lean_ctor_get(v_x_5846_, 4);
                if crate::leanh::lean_obj_tag(v_r_5847_) == 0 {
                    v_x_5846_ = v_r_5847_;
                    state = 0;
                    continue;
                } else {
                    v_k_5849_ = crate::leanh::lean_ctor_get(v_x_5846_, 1);
                    v_v_5850_ = crate::leanh::lean_ctor_get(v_x_5846_, 2);
                    crate::leanh::lean_inc(v_v_5850_);
                    crate::leanh::lean_inc(v_k_5849_);
                    v___x_5851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5851_, 0, v_k_5849_);
                    crate::leanh::lean_ctor_set(v___x_5851_, 1, v_v_5850_);
                    return v___x_5851_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(
    mut v_x_5852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5853_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_5852_);
    crate::leanh::lean_dec(v_x_5852_);
    return v_res_5853_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry(
    mut v_00_u03b1_5854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5855_: *mut crate::leanh::LeanObject,
    mut v_x_5856_: *mut crate::leanh::LeanObject,
    mut v_x_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5858_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_5856_);
    return v___x_5858_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(
    mut v_00_u03b1_5859_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5860_: *mut crate::leanh::LeanObject,
    mut v_x_5861_: *mut crate::leanh::LeanObject,
    mut v_x_5862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5863_ = l_Std_DTreeMap_Internal_Impl_maxEntry(
        v_00_u03b1_5859_,
        v_00_u03b2_5860_,
        v_x_5861_,
        v_x_5862_,
    );
    crate::leanh::lean_dec(v_x_5861_);
    return v_res_5863_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(
    mut v_x_5864_: *mut crate::leanh::LeanObject,
    mut v_h__1_5865_: *mut crate::leanh::LeanObject,
    mut v_h__2_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_5867_ = crate::leanh::lean_ctor_get(v_x_5864_, 4);
    if crate::leanh::lean_obj_tag(v_r_5867_) == 0 {
        let mut v_size_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_5867_);
        crate::leanh::lean_dec(v_h__1_5865_);
        v_size_5868_ = crate::leanh::lean_ctor_get(v_x_5864_, 0);
        crate::leanh::lean_inc(v_size_5868_);
        v_k_5869_ = crate::leanh::lean_ctor_get(v_x_5864_, 1);
        crate::leanh::lean_inc(v_k_5869_);
        v_v_5870_ = crate::leanh::lean_ctor_get(v_x_5864_, 2);
        crate::leanh::lean_inc(v_v_5870_);
        v_l_5871_ = crate::leanh::lean_ctor_get(v_x_5864_, 3);
        crate::leanh::lean_inc(v_l_5871_);
        crate::leanh::lean_dec(v_x_5864_);
        v_size_5872_ = crate::leanh::lean_ctor_get(v_r_5867_, 0);
        crate::leanh::lean_inc(v_size_5872_);
        v_k_5873_ = crate::leanh::lean_ctor_get(v_r_5867_, 1);
        crate::leanh::lean_inc(v_k_5873_);
        v_v_5874_ = crate::leanh::lean_ctor_get(v_r_5867_, 2);
        crate::leanh::lean_inc(v_v_5874_);
        v_l_5875_ = crate::leanh::lean_ctor_get(v_r_5867_, 3);
        crate::leanh::lean_inc(v_l_5875_);
        v_r_5876_ = crate::leanh::lean_ctor_get(v_r_5867_, 4);
        crate::leanh::lean_inc(v_r_5876_);
        crate::leanh::lean_dec_ref_known(v_r_5867_, 5);
        v___x_5877_ = crate::leanh::lean_apply_10(
            v_h__2_5866_,
            v_size_5868_,
            v_k_5869_,
            v_v_5870_,
            v_l_5871_,
            v_size_5872_,
            v_k_5873_,
            v_v_5874_,
            v_l_5875_,
            v_r_5876_,
            crate::leanh::lean_box(0),
        );
        return v___x_5877_;
    } else {
        let mut v_size_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5866_);
        v_size_5878_ = crate::leanh::lean_ctor_get(v_x_5864_, 0);
        crate::leanh::lean_inc(v_size_5878_);
        v_k_5879_ = crate::leanh::lean_ctor_get(v_x_5864_, 1);
        crate::leanh::lean_inc(v_k_5879_);
        v_v_5880_ = crate::leanh::lean_ctor_get(v_x_5864_, 2);
        crate::leanh::lean_inc(v_v_5880_);
        v_l_5881_ = crate::leanh::lean_ctor_get(v_x_5864_, 3);
        crate::leanh::lean_inc(v_l_5881_);
        crate::leanh::lean_dec(v_x_5864_);
        v___x_5882_ = crate::leanh::lean_apply_5(
            v_h__1_5865_,
            v_size_5878_,
            v_k_5879_,
            v_v_5880_,
            v_l_5881_,
            crate::leanh::lean_box(0),
        );
        return v___x_5882_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(
    mut v_00_u03b1_5883_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5884_: *mut crate::leanh::LeanObject,
    mut v_motive_5885_: *mut crate::leanh::LeanObject,
    mut v_x_5886_: *mut crate::leanh::LeanObject,
    mut v_x_5887_: *mut crate::leanh::LeanObject,
    mut v_h__1_5888_: *mut crate::leanh::LeanObject,
    mut v_h__2_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_5890_ = crate::leanh::lean_ctor_get(v_x_5886_, 4);
    if crate::leanh::lean_obj_tag(v_r_5890_) == 0 {
        let mut v_size_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_5890_);
        crate::leanh::lean_dec(v_h__1_5888_);
        v_size_5891_ = crate::leanh::lean_ctor_get(v_x_5886_, 0);
        crate::leanh::lean_inc(v_size_5891_);
        v_k_5892_ = crate::leanh::lean_ctor_get(v_x_5886_, 1);
        crate::leanh::lean_inc(v_k_5892_);
        v_v_5893_ = crate::leanh::lean_ctor_get(v_x_5886_, 2);
        crate::leanh::lean_inc(v_v_5893_);
        v_l_5894_ = crate::leanh::lean_ctor_get(v_x_5886_, 3);
        crate::leanh::lean_inc(v_l_5894_);
        crate::leanh::lean_dec(v_x_5886_);
        v_size_5895_ = crate::leanh::lean_ctor_get(v_r_5890_, 0);
        crate::leanh::lean_inc(v_size_5895_);
        v_k_5896_ = crate::leanh::lean_ctor_get(v_r_5890_, 1);
        crate::leanh::lean_inc(v_k_5896_);
        v_v_5897_ = crate::leanh::lean_ctor_get(v_r_5890_, 2);
        crate::leanh::lean_inc(v_v_5897_);
        v_l_5898_ = crate::leanh::lean_ctor_get(v_r_5890_, 3);
        crate::leanh::lean_inc(v_l_5898_);
        v_r_5899_ = crate::leanh::lean_ctor_get(v_r_5890_, 4);
        crate::leanh::lean_inc(v_r_5899_);
        crate::leanh::lean_dec_ref_known(v_r_5890_, 5);
        v___x_5900_ = crate::leanh::lean_apply_10(
            v_h__2_5889_,
            v_size_5891_,
            v_k_5892_,
            v_v_5893_,
            v_l_5894_,
            v_size_5895_,
            v_k_5896_,
            v_v_5897_,
            v_l_5898_,
            v_r_5899_,
            crate::leanh::lean_box(0),
        );
        return v___x_5900_;
    } else {
        let mut v_size_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5889_);
        v_size_5901_ = crate::leanh::lean_ctor_get(v_x_5886_, 0);
        crate::leanh::lean_inc(v_size_5901_);
        v_k_5902_ = crate::leanh::lean_ctor_get(v_x_5886_, 1);
        crate::leanh::lean_inc(v_k_5902_);
        v_v_5903_ = crate::leanh::lean_ctor_get(v_x_5886_, 2);
        crate::leanh::lean_inc(v_v_5903_);
        v_l_5904_ = crate::leanh::lean_ctor_get(v_x_5886_, 3);
        crate::leanh::lean_inc(v_l_5904_);
        crate::leanh::lean_dec(v_x_5886_);
        v___x_5905_ = crate::leanh::lean_apply_5(
            v_h__1_5888_,
            v_size_5901_,
            v_k_5902_,
            v_v_5903_,
            v_l_5904_,
            crate::leanh::lean_box(0),
        );
        return v___x_5905_;
    }
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5907_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_5908_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_5909_ = crate::leanh::lean_unsigned_to_nat(390);
    v___x_5910_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0;
    v___x_5911_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_5912_ = l_mkPanicMessageWithDecl(
        v___x_5911_,
        v___x_5910_,
        v___x_5909_,
        v___x_5908_,
        v___x_5907_,
    );
    return v___x_5912_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(
    mut v_inst_5913_: *mut crate::leanh::LeanObject,
    mut v_x_5914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5914_) == 0 {
                    v_r_5915_ = crate::leanh::lean_ctor_get(v_x_5914_, 4);
                    if crate::leanh::lean_obj_tag(v_r_5915_) == 0 {
                        v_x_5914_ = v_r_5915_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5917_ = crate::leanh::lean_ctor_get(v_x_5914_, 1);
                        v_v_5918_ = crate::leanh::lean_ctor_get(v_x_5914_, 2);
                        crate::leanh::lean_inc(v_v_5918_);
                        crate::leanh::lean_inc(v_k_5917_);
                        v___x_5919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5919_, 0, v_k_5917_);
                        crate::leanh::lean_ctor_set(v___x_5919_, 1, v_v_5918_);
                        return v___x_5919_;
                    }
                } else {
                    v___x_5920_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1,
                    );
                    v___x_5921_ = l_panic___redArg(v_inst_5913_, v___x_5920_);
                    return v___x_5921_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(
    mut v_inst_5922_: *mut crate::leanh::LeanObject,
    mut v_x_5923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5924_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_5922_, v_x_5923_);
    crate::leanh::lean_dec(v_x_5923_);
    crate::leanh::lean_dec_ref(v_inst_5922_);
    return v_res_5924_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x21(
    mut v_00_u03b1_5925_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5926_: *mut crate::leanh::LeanObject,
    mut v_inst_5927_: *mut crate::leanh::LeanObject,
    mut v_x_5928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5929_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_5927_, v_x_5928_);
    return v___x_5929_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(
    mut v_00_u03b1_5930_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5931_: *mut crate::leanh::LeanObject,
    mut v_inst_5932_: *mut crate::leanh::LeanObject,
    mut v_x_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5934_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(
        v_00_u03b1_5930_,
        v_00_u03b2_5931_,
        v_inst_5932_,
        v_x_5933_,
    );
    crate::leanh::lean_dec(v_x_5933_);
    crate::leanh::lean_dec_ref(v_inst_5932_);
    return v_res_5934_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(
    mut v_x_5935_: *mut crate::leanh::LeanObject,
    mut v_x_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5935_) == 0 {
                    v_r_5937_ = crate::leanh::lean_ctor_get(v_x_5935_, 4);
                    if crate::leanh::lean_obj_tag(v_r_5937_) == 0 {
                        v_x_5935_ = v_r_5937_;
                        state = 0;
                        continue;
                    } else {
                        v_k_5939_ = crate::leanh::lean_ctor_get(v_x_5935_, 1);
                        v_v_5940_ = crate::leanh::lean_ctor_get(v_x_5935_, 2);
                        crate::leanh::lean_inc(v_v_5940_);
                        crate::leanh::lean_inc(v_k_5939_);
                        v___x_5941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5941_, 0, v_k_5939_);
                        crate::leanh::lean_ctor_set(v___x_5941_, 1, v_v_5940_);
                        return v___x_5941_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_x_5936_);
                    return v_x_5936_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(
    mut v_x_5942_: *mut crate::leanh::LeanObject,
    mut v_x_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_5942_, v_x_5943_);
    crate::leanh::lean_dec_ref(v_x_5943_);
    crate::leanh::lean_dec(v_x_5942_);
    return v_res_5944_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntryD(
    mut v_00_u03b1_5945_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5946_: *mut crate::leanh::LeanObject,
    mut v_x_5947_: *mut crate::leanh::LeanObject,
    mut v_x_5948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5949_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_5947_, v_x_5948_);
    return v___x_5949_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(
    mut v_00_u03b1_5950_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5951_: *mut crate::leanh::LeanObject,
    mut v_x_5952_: *mut crate::leanh::LeanObject,
    mut v_x_5953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5954_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(
        v_00_u03b1_5950_,
        v_00_u03b2_5951_,
        v_x_5952_,
        v_x_5953_,
    );
    crate::leanh::lean_dec_ref(v_x_5953_);
    crate::leanh::lean_dec(v_x_5952_);
    return v_res_5954_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(
    mut v_x_5955_: *mut crate::leanh::LeanObject,
    mut v_x_5956_: *mut crate::leanh::LeanObject,
    mut v_h__1_5957_: *mut crate::leanh::LeanObject,
    mut v_h__2_5958_: *mut crate::leanh::LeanObject,
    mut v_h__3_5959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5955_) == 0 {
        let mut v_r_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5957_);
        v_r_5960_ = crate::leanh::lean_ctor_get(v_x_5955_, 4);
        if crate::leanh::lean_obj_tag(v_r_5960_) == 0 {
            let mut v_size_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_5960_);
            crate::leanh::lean_dec(v_h__2_5958_);
            v_size_5961_ = crate::leanh::lean_ctor_get(v_x_5955_, 0);
            crate::leanh::lean_inc(v_size_5961_);
            v_k_5962_ = crate::leanh::lean_ctor_get(v_x_5955_, 1);
            crate::leanh::lean_inc(v_k_5962_);
            v_v_5963_ = crate::leanh::lean_ctor_get(v_x_5955_, 2);
            crate::leanh::lean_inc(v_v_5963_);
            v_l_5964_ = crate::leanh::lean_ctor_get(v_x_5955_, 3);
            crate::leanh::lean_inc(v_l_5964_);
            crate::leanh::lean_dec_ref_known(v_x_5955_, 5);
            v_size_5965_ = crate::leanh::lean_ctor_get(v_r_5960_, 0);
            crate::leanh::lean_inc(v_size_5965_);
            v_k_5966_ = crate::leanh::lean_ctor_get(v_r_5960_, 1);
            crate::leanh::lean_inc(v_k_5966_);
            v_v_5967_ = crate::leanh::lean_ctor_get(v_r_5960_, 2);
            crate::leanh::lean_inc(v_v_5967_);
            v_l_5968_ = crate::leanh::lean_ctor_get(v_r_5960_, 3);
            crate::leanh::lean_inc(v_l_5968_);
            v_r_5969_ = crate::leanh::lean_ctor_get(v_r_5960_, 4);
            crate::leanh::lean_inc(v_r_5969_);
            crate::leanh::lean_dec_ref_known(v_r_5960_, 5);
            v___x_5970_ = crate::leanh::lean_apply_10(
                v_h__3_5959_,
                v_size_5961_,
                v_k_5962_,
                v_v_5963_,
                v_l_5964_,
                v_size_5965_,
                v_k_5966_,
                v_v_5967_,
                v_l_5968_,
                v_r_5969_,
                v_x_5956_,
            );
            return v___x_5970_;
        } else {
            let mut v_size_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5959_);
            v_size_5971_ = crate::leanh::lean_ctor_get(v_x_5955_, 0);
            crate::leanh::lean_inc(v_size_5971_);
            v_k_5972_ = crate::leanh::lean_ctor_get(v_x_5955_, 1);
            crate::leanh::lean_inc(v_k_5972_);
            v_v_5973_ = crate::leanh::lean_ctor_get(v_x_5955_, 2);
            crate::leanh::lean_inc(v_v_5973_);
            v_l_5974_ = crate::leanh::lean_ctor_get(v_x_5955_, 3);
            crate::leanh::lean_inc(v_l_5974_);
            crate::leanh::lean_dec_ref_known(v_x_5955_, 5);
            v___x_5975_ = crate::leanh::lean_apply_5(
                v_h__2_5958_,
                v_size_5971_,
                v_k_5972_,
                v_v_5973_,
                v_l_5974_,
                v_x_5956_,
            );
            return v___x_5975_;
        }
    } else {
        let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5959_);
        crate::leanh::lean_dec(v_h__2_5958_);
        v___x_5976_ = crate::leanh::lean_apply_1(v_h__1_5957_, v_x_5956_);
        return v___x_5976_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(
    mut v_00_u03b1_5977_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5978_: *mut crate::leanh::LeanObject,
    mut v_motive_5979_: *mut crate::leanh::LeanObject,
    mut v_x_5980_: *mut crate::leanh::LeanObject,
    mut v_x_5981_: *mut crate::leanh::LeanObject,
    mut v_h__1_5982_: *mut crate::leanh::LeanObject,
    mut v_h__2_5983_: *mut crate::leanh::LeanObject,
    mut v_h__3_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5980_) == 0 {
        let mut v_r_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5982_);
        v_r_5985_ = crate::leanh::lean_ctor_get(v_x_5980_, 4);
        if crate::leanh::lean_obj_tag(v_r_5985_) == 0 {
            let mut v_size_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_5985_);
            crate::leanh::lean_dec(v_h__2_5983_);
            v_size_5986_ = crate::leanh::lean_ctor_get(v_x_5980_, 0);
            crate::leanh::lean_inc(v_size_5986_);
            v_k_5987_ = crate::leanh::lean_ctor_get(v_x_5980_, 1);
            crate::leanh::lean_inc(v_k_5987_);
            v_v_5988_ = crate::leanh::lean_ctor_get(v_x_5980_, 2);
            crate::leanh::lean_inc(v_v_5988_);
            v_l_5989_ = crate::leanh::lean_ctor_get(v_x_5980_, 3);
            crate::leanh::lean_inc(v_l_5989_);
            crate::leanh::lean_dec_ref_known(v_x_5980_, 5);
            v_size_5990_ = crate::leanh::lean_ctor_get(v_r_5985_, 0);
            crate::leanh::lean_inc(v_size_5990_);
            v_k_5991_ = crate::leanh::lean_ctor_get(v_r_5985_, 1);
            crate::leanh::lean_inc(v_k_5991_);
            v_v_5992_ = crate::leanh::lean_ctor_get(v_r_5985_, 2);
            crate::leanh::lean_inc(v_v_5992_);
            v_l_5993_ = crate::leanh::lean_ctor_get(v_r_5985_, 3);
            crate::leanh::lean_inc(v_l_5993_);
            v_r_5994_ = crate::leanh::lean_ctor_get(v_r_5985_, 4);
            crate::leanh::lean_inc(v_r_5994_);
            crate::leanh::lean_dec_ref_known(v_r_5985_, 5);
            v___x_5995_ = crate::leanh::lean_apply_10(
                v_h__3_5984_,
                v_size_5986_,
                v_k_5987_,
                v_v_5988_,
                v_l_5989_,
                v_size_5990_,
                v_k_5991_,
                v_v_5992_,
                v_l_5993_,
                v_r_5994_,
                v_x_5981_,
            );
            return v___x_5995_;
        } else {
            let mut v_size_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_5984_);
            v_size_5996_ = crate::leanh::lean_ctor_get(v_x_5980_, 0);
            crate::leanh::lean_inc(v_size_5996_);
            v_k_5997_ = crate::leanh::lean_ctor_get(v_x_5980_, 1);
            crate::leanh::lean_inc(v_k_5997_);
            v_v_5998_ = crate::leanh::lean_ctor_get(v_x_5980_, 2);
            crate::leanh::lean_inc(v_v_5998_);
            v_l_5999_ = crate::leanh::lean_ctor_get(v_x_5980_, 3);
            crate::leanh::lean_inc(v_l_5999_);
            crate::leanh::lean_dec_ref_known(v_x_5980_, 5);
            v___x_6000_ = crate::leanh::lean_apply_5(
                v_h__2_5983_,
                v_size_5996_,
                v_k_5997_,
                v_v_5998_,
                v_l_5999_,
                v_x_5981_,
            );
            return v___x_6000_;
        }
    } else {
        let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_5984_);
        crate::leanh::lean_dec(v_h__2_5983_);
        v___x_6001_ = crate::leanh::lean_apply_1(v_h__1_5982_, v_x_5981_);
        return v___x_6001_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(
    mut v_x_6002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6002_) == 0 {
                    v_l_6003_ = crate::leanh::lean_ctor_get(v_x_6002_, 3);
                    if crate::leanh::lean_obj_tag(v_l_6003_) == 0 {
                        v_x_6002_ = v_l_6003_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6005_ = crate::leanh::lean_ctor_get(v_x_6002_, 1);
                        crate::leanh::lean_inc(v_k_6005_);
                        v___x_6006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6006_, 0, v_k_6005_);
                        return v___x_6006_;
                    }
                } else {
                    v___x_6007_ = crate::leanh::lean_box(0);
                    return v___x_6007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(
    mut v_x_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6009_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_6008_);
    crate::leanh::lean_dec(v_x_6008_);
    return v_res_6009_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x3f(
    mut v_00_u03b1_6010_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6011_: *mut crate::leanh::LeanObject,
    mut v_x_6012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6013_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_6012_);
    return v___x_6013_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(
    mut v_00_u03b1_6014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6015_: *mut crate::leanh::LeanObject,
    mut v_x_6016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6017_ =
        l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_6014_, v_00_u03b2_6015_, v_x_6016_);
    crate::leanh::lean_dec(v_x_6016_);
    return v_res_6017_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey___redArg(
    mut v_x_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_l_6019_ = crate::leanh::lean_ctor_get(v_x_6018_, 3);
                if crate::leanh::lean_obj_tag(v_l_6019_) == 0 {
                    v_x_6018_ = v_l_6019_;
                    state = 0;
                    continue;
                } else {
                    v_k_6021_ = crate::leanh::lean_ctor_get(v_x_6018_, 1);
                    crate::leanh::lean_inc(v_k_6021_);
                    return v_k_6021_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(
    mut v_x_6022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6023_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_6022_);
    crate::leanh::lean_dec(v_x_6022_);
    return v_res_6023_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey(
    mut v_00_u03b1_6024_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6025_: *mut crate::leanh::LeanObject,
    mut v_x_6026_: *mut crate::leanh::LeanObject,
    mut v_x_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6028_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_6026_);
    return v___x_6028_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey___boxed(
    mut v_00_u03b1_6029_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6030_: *mut crate::leanh::LeanObject,
    mut v_x_6031_: *mut crate::leanh::LeanObject,
    mut v_x_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6033_ = l_Std_DTreeMap_Internal_Impl_minKey(
        v_00_u03b1_6029_,
        v_00_u03b2_6030_,
        v_x_6031_,
        v_x_6032_,
    );
    crate::leanh::lean_dec(v_x_6031_);
    return v_res_6033_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6035_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_6036_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_6037_ = crate::leanh::lean_unsigned_to_nat(413);
    v___x_6038_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0;
    v___x_6039_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_6040_ = l_mkPanicMessageWithDecl(
        v___x_6039_,
        v___x_6038_,
        v___x_6037_,
        v___x_6036_,
        v___x_6035_,
    );
    return v___x_6040_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(
    mut v_inst_6041_: *mut crate::leanh::LeanObject,
    mut v_x_6042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6042_) == 0 {
                    v_l_6043_ = crate::leanh::lean_ctor_get(v_x_6042_, 3);
                    if crate::leanh::lean_obj_tag(v_l_6043_) == 0 {
                        v_x_6042_ = v_l_6043_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6045_ = crate::leanh::lean_ctor_get(v_x_6042_, 1);
                        crate::leanh::lean_inc(v_k_6045_);
                        return v_k_6045_;
                    }
                } else {
                    v___x_6046_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1,
                    );
                    v___x_6047_ = l_panic___redArg(v_inst_6041_, v___x_6046_);
                    return v___x_6047_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(
    mut v_inst_6048_: *mut crate::leanh::LeanObject,
    mut v_x_6049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6050_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_6048_, v_x_6049_);
    crate::leanh::lean_dec(v_x_6049_);
    crate::leanh::lean_dec(v_inst_6048_);
    return v_res_6050_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x21(
    mut v_00_u03b1_6051_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6052_: *mut crate::leanh::LeanObject,
    mut v_inst_6053_: *mut crate::leanh::LeanObject,
    mut v_x_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_6053_, v_x_6054_);
    return v___x_6055_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(
    mut v_00_u03b1_6056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6057_: *mut crate::leanh::LeanObject,
    mut v_inst_6058_: *mut crate::leanh::LeanObject,
    mut v_x_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(
        v_00_u03b1_6056_,
        v_00_u03b2_6057_,
        v_inst_6058_,
        v_x_6059_,
    );
    crate::leanh::lean_dec(v_x_6059_);
    crate::leanh::lean_dec(v_inst_6058_);
    return v_res_6060_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(
    mut v_x_6061_: *mut crate::leanh::LeanObject,
    mut v_x_6062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6061_) == 0 {
                    v_l_6063_ = crate::leanh::lean_ctor_get(v_x_6061_, 3);
                    if crate::leanh::lean_obj_tag(v_l_6063_) == 0 {
                        v_x_6061_ = v_l_6063_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6065_ = crate::leanh::lean_ctor_get(v_x_6061_, 1);
                        crate::leanh::lean_inc(v_k_6065_);
                        return v_k_6065_;
                    }
                } else {
                    crate::leanh::lean_inc(v_x_6062_);
                    return v_x_6062_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(
    mut v_x_6066_: *mut crate::leanh::LeanObject,
    mut v_x_6067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_6066_, v_x_6067_);
    crate::leanh::lean_dec(v_x_6067_);
    crate::leanh::lean_dec(v_x_6066_);
    return v_res_6068_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKeyD(
    mut v_00_u03b1_6069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6070_: *mut crate::leanh::LeanObject,
    mut v_x_6071_: *mut crate::leanh::LeanObject,
    mut v_x_6072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6073_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_6071_, v_x_6072_);
    return v___x_6073_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(
    mut v_00_u03b1_6074_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6075_: *mut crate::leanh::LeanObject,
    mut v_x_6076_: *mut crate::leanh::LeanObject,
    mut v_x_6077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6078_ = l_Std_DTreeMap_Internal_Impl_minKeyD(
        v_00_u03b1_6074_,
        v_00_u03b2_6075_,
        v_x_6076_,
        v_x_6077_,
    );
    crate::leanh::lean_dec(v_x_6077_);
    crate::leanh::lean_dec(v_x_6076_);
    return v_res_6078_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(
    mut v_x_6079_: *mut crate::leanh::LeanObject,
    mut v_x_6080_: *mut crate::leanh::LeanObject,
    mut v_h__1_6081_: *mut crate::leanh::LeanObject,
    mut v_h__2_6082_: *mut crate::leanh::LeanObject,
    mut v_h__3_6083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6079_) == 0 {
        let mut v_l_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6081_);
        v_l_6084_ = crate::leanh::lean_ctor_get(v_x_6079_, 3);
        if crate::leanh::lean_obj_tag(v_l_6084_) == 0 {
            let mut v_size_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_6084_);
            crate::leanh::lean_dec(v_h__2_6082_);
            v_size_6085_ = crate::leanh::lean_ctor_get(v_x_6079_, 0);
            crate::leanh::lean_inc(v_size_6085_);
            v_k_6086_ = crate::leanh::lean_ctor_get(v_x_6079_, 1);
            crate::leanh::lean_inc(v_k_6086_);
            v_v_6087_ = crate::leanh::lean_ctor_get(v_x_6079_, 2);
            crate::leanh::lean_inc(v_v_6087_);
            v_r_6088_ = crate::leanh::lean_ctor_get(v_x_6079_, 4);
            crate::leanh::lean_inc(v_r_6088_);
            crate::leanh::lean_dec_ref_known(v_x_6079_, 5);
            v_size_6089_ = crate::leanh::lean_ctor_get(v_l_6084_, 0);
            crate::leanh::lean_inc(v_size_6089_);
            v_k_6090_ = crate::leanh::lean_ctor_get(v_l_6084_, 1);
            crate::leanh::lean_inc(v_k_6090_);
            v_v_6091_ = crate::leanh::lean_ctor_get(v_l_6084_, 2);
            crate::leanh::lean_inc(v_v_6091_);
            v_l_6092_ = crate::leanh::lean_ctor_get(v_l_6084_, 3);
            crate::leanh::lean_inc(v_l_6092_);
            v_r_6093_ = crate::leanh::lean_ctor_get(v_l_6084_, 4);
            crate::leanh::lean_inc(v_r_6093_);
            crate::leanh::lean_dec_ref_known(v_l_6084_, 5);
            v___x_6094_ = crate::leanh::lean_apply_10(
                v_h__3_6083_,
                v_size_6085_,
                v_k_6086_,
                v_v_6087_,
                v_size_6089_,
                v_k_6090_,
                v_v_6091_,
                v_l_6092_,
                v_r_6093_,
                v_r_6088_,
                v_x_6080_,
            );
            return v___x_6094_;
        } else {
            let mut v_size_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6083_);
            v_size_6095_ = crate::leanh::lean_ctor_get(v_x_6079_, 0);
            crate::leanh::lean_inc(v_size_6095_);
            v_k_6096_ = crate::leanh::lean_ctor_get(v_x_6079_, 1);
            crate::leanh::lean_inc(v_k_6096_);
            v_v_6097_ = crate::leanh::lean_ctor_get(v_x_6079_, 2);
            crate::leanh::lean_inc(v_v_6097_);
            v_r_6098_ = crate::leanh::lean_ctor_get(v_x_6079_, 4);
            crate::leanh::lean_inc(v_r_6098_);
            crate::leanh::lean_dec_ref_known(v_x_6079_, 5);
            v___x_6099_ = crate::leanh::lean_apply_5(
                v_h__2_6082_,
                v_size_6095_,
                v_k_6096_,
                v_v_6097_,
                v_r_6098_,
                v_x_6080_,
            );
            return v___x_6099_;
        }
    } else {
        let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6083_);
        crate::leanh::lean_dec(v_h__2_6082_);
        v___x_6100_ = crate::leanh::lean_apply_1(v_h__1_6081_, v_x_6080_);
        return v___x_6100_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(
    mut v_00_u03b1_6101_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6102_: *mut crate::leanh::LeanObject,
    mut v_motive_6103_: *mut crate::leanh::LeanObject,
    mut v_x_6104_: *mut crate::leanh::LeanObject,
    mut v_x_6105_: *mut crate::leanh::LeanObject,
    mut v_h__1_6106_: *mut crate::leanh::LeanObject,
    mut v_h__2_6107_: *mut crate::leanh::LeanObject,
    mut v_h__3_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6104_) == 0 {
        let mut v_l_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6106_);
        v_l_6109_ = crate::leanh::lean_ctor_get(v_x_6104_, 3);
        if crate::leanh::lean_obj_tag(v_l_6109_) == 0 {
            let mut v_size_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_6109_);
            crate::leanh::lean_dec(v_h__2_6107_);
            v_size_6110_ = crate::leanh::lean_ctor_get(v_x_6104_, 0);
            crate::leanh::lean_inc(v_size_6110_);
            v_k_6111_ = crate::leanh::lean_ctor_get(v_x_6104_, 1);
            crate::leanh::lean_inc(v_k_6111_);
            v_v_6112_ = crate::leanh::lean_ctor_get(v_x_6104_, 2);
            crate::leanh::lean_inc(v_v_6112_);
            v_r_6113_ = crate::leanh::lean_ctor_get(v_x_6104_, 4);
            crate::leanh::lean_inc(v_r_6113_);
            crate::leanh::lean_dec_ref_known(v_x_6104_, 5);
            v_size_6114_ = crate::leanh::lean_ctor_get(v_l_6109_, 0);
            crate::leanh::lean_inc(v_size_6114_);
            v_k_6115_ = crate::leanh::lean_ctor_get(v_l_6109_, 1);
            crate::leanh::lean_inc(v_k_6115_);
            v_v_6116_ = crate::leanh::lean_ctor_get(v_l_6109_, 2);
            crate::leanh::lean_inc(v_v_6116_);
            v_l_6117_ = crate::leanh::lean_ctor_get(v_l_6109_, 3);
            crate::leanh::lean_inc(v_l_6117_);
            v_r_6118_ = crate::leanh::lean_ctor_get(v_l_6109_, 4);
            crate::leanh::lean_inc(v_r_6118_);
            crate::leanh::lean_dec_ref_known(v_l_6109_, 5);
            v___x_6119_ = crate::leanh::lean_apply_10(
                v_h__3_6108_,
                v_size_6110_,
                v_k_6111_,
                v_v_6112_,
                v_size_6114_,
                v_k_6115_,
                v_v_6116_,
                v_l_6117_,
                v_r_6118_,
                v_r_6113_,
                v_x_6105_,
            );
            return v___x_6119_;
        } else {
            let mut v_size_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6108_);
            v_size_6120_ = crate::leanh::lean_ctor_get(v_x_6104_, 0);
            crate::leanh::lean_inc(v_size_6120_);
            v_k_6121_ = crate::leanh::lean_ctor_get(v_x_6104_, 1);
            crate::leanh::lean_inc(v_k_6121_);
            v_v_6122_ = crate::leanh::lean_ctor_get(v_x_6104_, 2);
            crate::leanh::lean_inc(v_v_6122_);
            v_r_6123_ = crate::leanh::lean_ctor_get(v_x_6104_, 4);
            crate::leanh::lean_inc(v_r_6123_);
            crate::leanh::lean_dec_ref_known(v_x_6104_, 5);
            v___x_6124_ = crate::leanh::lean_apply_5(
                v_h__2_6107_,
                v_size_6120_,
                v_k_6121_,
                v_v_6122_,
                v_r_6123_,
                v_x_6105_,
            );
            return v___x_6124_;
        }
    } else {
        let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6108_);
        crate::leanh::lean_dec(v_h__2_6107_);
        v___x_6125_ = crate::leanh::lean_apply_1(v_h__1_6106_, v_x_6105_);
        return v___x_6125_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(
    mut v_x_6126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6126_) == 0 {
                    v_r_6127_ = crate::leanh::lean_ctor_get(v_x_6126_, 4);
                    if crate::leanh::lean_obj_tag(v_r_6127_) == 0 {
                        v_x_6126_ = v_r_6127_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6129_ = crate::leanh::lean_ctor_get(v_x_6126_, 1);
                        crate::leanh::lean_inc(v_k_6129_);
                        v___x_6130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6130_, 0, v_k_6129_);
                        return v___x_6130_;
                    }
                } else {
                    v___x_6131_ = crate::leanh::lean_box(0);
                    return v___x_6131_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(
    mut v_x_6132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6133_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_6132_);
    crate::leanh::lean_dec(v_x_6132_);
    return v_res_6133_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x3f(
    mut v_00_u03b1_6134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6135_: *mut crate::leanh::LeanObject,
    mut v_x_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6137_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_6136_);
    return v___x_6137_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(
    mut v_00_u03b1_6138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6139_: *mut crate::leanh::LeanObject,
    mut v_x_6140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6141_ =
        l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_6138_, v_00_u03b2_6139_, v_x_6140_);
    crate::leanh::lean_dec(v_x_6140_);
    return v_res_6141_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey___redArg(
    mut v_x_6142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_6143_ = crate::leanh::lean_ctor_get(v_x_6142_, 4);
                if crate::leanh::lean_obj_tag(v_r_6143_) == 0 {
                    v_x_6142_ = v_r_6143_;
                    state = 0;
                    continue;
                } else {
                    v_k_6145_ = crate::leanh::lean_ctor_get(v_x_6142_, 1);
                    crate::leanh::lean_inc(v_k_6145_);
                    return v_k_6145_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(
    mut v_x_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6147_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_6146_);
    crate::leanh::lean_dec(v_x_6146_);
    return v_res_6147_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey(
    mut v_00_u03b1_6148_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6149_: *mut crate::leanh::LeanObject,
    mut v_x_6150_: *mut crate::leanh::LeanObject,
    mut v_x_6151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6152_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_6150_);
    return v___x_6152_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey___boxed(
    mut v_00_u03b1_6153_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6154_: *mut crate::leanh::LeanObject,
    mut v_x_6155_: *mut crate::leanh::LeanObject,
    mut v_x_6156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Std_DTreeMap_Internal_Impl_maxKey(
        v_00_u03b1_6153_,
        v_00_u03b2_6154_,
        v_x_6155_,
        v_x_6156_,
    );
    crate::leanh::lean_dec(v_x_6155_);
    return v_res_6157_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6159_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_6160_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_6161_ = crate::leanh::lean_unsigned_to_nat(436);
    v___x_6162_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0;
    v___x_6163_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_6164_ = l_mkPanicMessageWithDecl(
        v___x_6163_,
        v___x_6162_,
        v___x_6161_,
        v___x_6160_,
        v___x_6159_,
    );
    return v___x_6164_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(
    mut v_inst_6165_: *mut crate::leanh::LeanObject,
    mut v_x_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6166_) == 0 {
                    v_r_6167_ = crate::leanh::lean_ctor_get(v_x_6166_, 4);
                    if crate::leanh::lean_obj_tag(v_r_6167_) == 0 {
                        v_x_6166_ = v_r_6167_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6169_ = crate::leanh::lean_ctor_get(v_x_6166_, 1);
                        crate::leanh::lean_inc(v_k_6169_);
                        return v_k_6169_;
                    }
                } else {
                    v___x_6170_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1,
                    );
                    v___x_6171_ = l_panic___redArg(v_inst_6165_, v___x_6170_);
                    return v___x_6171_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(
    mut v_inst_6172_: *mut crate::leanh::LeanObject,
    mut v_x_6173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6174_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_6172_, v_x_6173_);
    crate::leanh::lean_dec(v_x_6173_);
    crate::leanh::lean_dec(v_inst_6172_);
    return v_res_6174_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x21(
    mut v_00_u03b1_6175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6176_: *mut crate::leanh::LeanObject,
    mut v_inst_6177_: *mut crate::leanh::LeanObject,
    mut v_x_6178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_6177_, v_x_6178_);
    return v___x_6179_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(
    mut v_00_u03b1_6180_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6181_: *mut crate::leanh::LeanObject,
    mut v_inst_6182_: *mut crate::leanh::LeanObject,
    mut v_x_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6184_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(
        v_00_u03b1_6180_,
        v_00_u03b2_6181_,
        v_inst_6182_,
        v_x_6183_,
    );
    crate::leanh::lean_dec(v_x_6183_);
    crate::leanh::lean_dec(v_inst_6182_);
    return v_res_6184_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(
    mut v_x_6185_: *mut crate::leanh::LeanObject,
    mut v_x_6186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6185_) == 0 {
                    v_r_6187_ = crate::leanh::lean_ctor_get(v_x_6185_, 4);
                    if crate::leanh::lean_obj_tag(v_r_6187_) == 0 {
                        v_x_6185_ = v_r_6187_;
                        state = 0;
                        continue;
                    } else {
                        v_k_6189_ = crate::leanh::lean_ctor_get(v_x_6185_, 1);
                        crate::leanh::lean_inc(v_k_6189_);
                        return v_k_6189_;
                    }
                } else {
                    crate::leanh::lean_inc(v_x_6186_);
                    return v_x_6186_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(
    mut v_x_6190_: *mut crate::leanh::LeanObject,
    mut v_x_6191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6192_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_6190_, v_x_6191_);
    crate::leanh::lean_dec(v_x_6191_);
    crate::leanh::lean_dec(v_x_6190_);
    return v_res_6192_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKeyD(
    mut v_00_u03b1_6193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6194_: *mut crate::leanh::LeanObject,
    mut v_x_6195_: *mut crate::leanh::LeanObject,
    mut v_x_6196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6197_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_6195_, v_x_6196_);
    return v___x_6197_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(
    mut v_00_u03b1_6198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6199_: *mut crate::leanh::LeanObject,
    mut v_x_6200_: *mut crate::leanh::LeanObject,
    mut v_x_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(
        v_00_u03b1_6198_,
        v_00_u03b2_6199_,
        v_x_6200_,
        v_x_6201_,
    );
    crate::leanh::lean_dec(v_x_6201_);
    crate::leanh::lean_dec(v_x_6200_);
    return v_res_6202_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(
    mut v_x_6203_: *mut crate::leanh::LeanObject,
    mut v_x_6204_: *mut crate::leanh::LeanObject,
    mut v_h__1_6205_: *mut crate::leanh::LeanObject,
    mut v_h__2_6206_: *mut crate::leanh::LeanObject,
    mut v_h__3_6207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6203_) == 0 {
        let mut v_r_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6205_);
        v_r_6208_ = crate::leanh::lean_ctor_get(v_x_6203_, 4);
        if crate::leanh::lean_obj_tag(v_r_6208_) == 0 {
            let mut v_size_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_6208_);
            crate::leanh::lean_dec(v_h__2_6206_);
            v_size_6209_ = crate::leanh::lean_ctor_get(v_x_6203_, 0);
            crate::leanh::lean_inc(v_size_6209_);
            v_k_6210_ = crate::leanh::lean_ctor_get(v_x_6203_, 1);
            crate::leanh::lean_inc(v_k_6210_);
            v_v_6211_ = crate::leanh::lean_ctor_get(v_x_6203_, 2);
            crate::leanh::lean_inc(v_v_6211_);
            v_l_6212_ = crate::leanh::lean_ctor_get(v_x_6203_, 3);
            crate::leanh::lean_inc(v_l_6212_);
            crate::leanh::lean_dec_ref_known(v_x_6203_, 5);
            v_size_6213_ = crate::leanh::lean_ctor_get(v_r_6208_, 0);
            crate::leanh::lean_inc(v_size_6213_);
            v_k_6214_ = crate::leanh::lean_ctor_get(v_r_6208_, 1);
            crate::leanh::lean_inc(v_k_6214_);
            v_v_6215_ = crate::leanh::lean_ctor_get(v_r_6208_, 2);
            crate::leanh::lean_inc(v_v_6215_);
            v_l_6216_ = crate::leanh::lean_ctor_get(v_r_6208_, 3);
            crate::leanh::lean_inc(v_l_6216_);
            v_r_6217_ = crate::leanh::lean_ctor_get(v_r_6208_, 4);
            crate::leanh::lean_inc(v_r_6217_);
            crate::leanh::lean_dec_ref_known(v_r_6208_, 5);
            v___x_6218_ = crate::leanh::lean_apply_10(
                v_h__3_6207_,
                v_size_6209_,
                v_k_6210_,
                v_v_6211_,
                v_l_6212_,
                v_size_6213_,
                v_k_6214_,
                v_v_6215_,
                v_l_6216_,
                v_r_6217_,
                v_x_6204_,
            );
            return v___x_6218_;
        } else {
            let mut v_size_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6207_);
            v_size_6219_ = crate::leanh::lean_ctor_get(v_x_6203_, 0);
            crate::leanh::lean_inc(v_size_6219_);
            v_k_6220_ = crate::leanh::lean_ctor_get(v_x_6203_, 1);
            crate::leanh::lean_inc(v_k_6220_);
            v_v_6221_ = crate::leanh::lean_ctor_get(v_x_6203_, 2);
            crate::leanh::lean_inc(v_v_6221_);
            v_l_6222_ = crate::leanh::lean_ctor_get(v_x_6203_, 3);
            crate::leanh::lean_inc(v_l_6222_);
            crate::leanh::lean_dec_ref_known(v_x_6203_, 5);
            v___x_6223_ = crate::leanh::lean_apply_5(
                v_h__2_6206_,
                v_size_6219_,
                v_k_6220_,
                v_v_6221_,
                v_l_6222_,
                v_x_6204_,
            );
            return v___x_6223_;
        }
    } else {
        let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6207_);
        crate::leanh::lean_dec(v_h__2_6206_);
        v___x_6224_ = crate::leanh::lean_apply_1(v_h__1_6205_, v_x_6204_);
        return v___x_6224_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(
    mut v_00_u03b1_6225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6226_: *mut crate::leanh::LeanObject,
    mut v_motive_6227_: *mut crate::leanh::LeanObject,
    mut v_x_6228_: *mut crate::leanh::LeanObject,
    mut v_x_6229_: *mut crate::leanh::LeanObject,
    mut v_h__1_6230_: *mut crate::leanh::LeanObject,
    mut v_h__2_6231_: *mut crate::leanh::LeanObject,
    mut v_h__3_6232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6228_) == 0 {
        let mut v_r_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6230_);
        v_r_6233_ = crate::leanh::lean_ctor_get(v_x_6228_, 4);
        if crate::leanh::lean_obj_tag(v_r_6233_) == 0 {
            let mut v_size_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_6233_);
            crate::leanh::lean_dec(v_h__2_6231_);
            v_size_6234_ = crate::leanh::lean_ctor_get(v_x_6228_, 0);
            crate::leanh::lean_inc(v_size_6234_);
            v_k_6235_ = crate::leanh::lean_ctor_get(v_x_6228_, 1);
            crate::leanh::lean_inc(v_k_6235_);
            v_v_6236_ = crate::leanh::lean_ctor_get(v_x_6228_, 2);
            crate::leanh::lean_inc(v_v_6236_);
            v_l_6237_ = crate::leanh::lean_ctor_get(v_x_6228_, 3);
            crate::leanh::lean_inc(v_l_6237_);
            crate::leanh::lean_dec_ref_known(v_x_6228_, 5);
            v_size_6238_ = crate::leanh::lean_ctor_get(v_r_6233_, 0);
            crate::leanh::lean_inc(v_size_6238_);
            v_k_6239_ = crate::leanh::lean_ctor_get(v_r_6233_, 1);
            crate::leanh::lean_inc(v_k_6239_);
            v_v_6240_ = crate::leanh::lean_ctor_get(v_r_6233_, 2);
            crate::leanh::lean_inc(v_v_6240_);
            v_l_6241_ = crate::leanh::lean_ctor_get(v_r_6233_, 3);
            crate::leanh::lean_inc(v_l_6241_);
            v_r_6242_ = crate::leanh::lean_ctor_get(v_r_6233_, 4);
            crate::leanh::lean_inc(v_r_6242_);
            crate::leanh::lean_dec_ref_known(v_r_6233_, 5);
            v___x_6243_ = crate::leanh::lean_apply_10(
                v_h__3_6232_,
                v_size_6234_,
                v_k_6235_,
                v_v_6236_,
                v_l_6237_,
                v_size_6238_,
                v_k_6239_,
                v_v_6240_,
                v_l_6241_,
                v_r_6242_,
                v_x_6229_,
            );
            return v___x_6243_;
        } else {
            let mut v_size_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6232_);
            v_size_6244_ = crate::leanh::lean_ctor_get(v_x_6228_, 0);
            crate::leanh::lean_inc(v_size_6244_);
            v_k_6245_ = crate::leanh::lean_ctor_get(v_x_6228_, 1);
            crate::leanh::lean_inc(v_k_6245_);
            v_v_6246_ = crate::leanh::lean_ctor_get(v_x_6228_, 2);
            crate::leanh::lean_inc(v_v_6246_);
            v_l_6247_ = crate::leanh::lean_ctor_get(v_x_6228_, 3);
            crate::leanh::lean_inc(v_l_6247_);
            crate::leanh::lean_dec_ref_known(v_x_6228_, 5);
            v___x_6248_ = crate::leanh::lean_apply_5(
                v_h__2_6231_,
                v_size_6244_,
                v_k_6245_,
                v_v_6246_,
                v_l_6247_,
                v_x_6229_,
            );
            return v___x_6248_;
        }
    } else {
        let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6232_);
        crate::leanh::lean_dec(v_h__2_6231_);
        v___x_6249_ = crate::leanh::lean_apply_1(v_h__1_6230_, v_x_6229_);
        return v___x_6249_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(
    mut v_x_6250_: *mut crate::leanh::LeanObject,
    mut v_x_6251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: u8 = 0;
    let mut v___x_6265_: u8 = 0;
    let mut v_size_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_6252_ = crate::leanh::lean_ctor_get(v_x_6250_, 1);
                v_v_6253_ = crate::leanh::lean_ctor_get(v_x_6250_, 2);
                v_l_6254_ = crate::leanh::lean_ctor_get(v_x_6250_, 3);
                v_r_6255_ = crate::leanh::lean_ctor_get(v_x_6250_, 4);
                if crate::leanh::lean_obj_tag(v_l_6254_) == 0 {
                    v_size_6270_ = crate::leanh::lean_ctor_get(v_l_6254_, 0);
                    v___y_6263_ = v_size_6270_;
                    state = 2;
                    continue;
                } else {
                    v___x_6271_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6263_ = v___x_6271_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6258_ = lean_nat_sub(v_x_6251_, v___y_6257_);
                crate::leanh::lean_dec(v_x_6251_);
                v___x_6259_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6260_ = lean_nat_sub(v___x_6258_, v___x_6259_);
                crate::leanh::lean_dec(v___x_6258_);
                v_x_6250_ = v_r_6255_;
                v_x_6251_ = v___x_6260_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6264_ = lean_nat_dec_lt(v_x_6251_, v___y_6263_);
                if v___x_6264_ == 0 {
                    v___x_6265_ = lean_nat_dec_eq(v_x_6251_, v___y_6263_);
                    if v___x_6265_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6254_) == 0 {
                            v_size_6266_ = crate::leanh::lean_ctor_get(v_l_6254_, 0);
                            v___y_6257_ = v_size_6266_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6267_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6257_ = v___x_6267_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6251_);
                        crate::leanh::lean_inc(v_v_6253_);
                        crate::leanh::lean_inc(v_k_6252_);
                        v___x_6268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6268_, 0, v_k_6252_);
                        crate::leanh::lean_ctor_set(v___x_6268_, 1, v_v_6253_);
                        return v___x_6268_;
                    }
                } else {
                    v_x_6250_ = v_l_6254_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(
    mut v_x_6272_: *mut crate::leanh::LeanObject,
    mut v_x_6273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6274_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_6272_, v_x_6273_);
    crate::leanh::lean_dec(v_x_6272_);
    return v_res_6274_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx(
    mut v_00_u03b1_6275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6276_: *mut crate::leanh::LeanObject,
    mut v_x_6277_: *mut crate::leanh::LeanObject,
    mut v_x_6278_: *mut crate::leanh::LeanObject,
    mut v_x_6279_: *mut crate::leanh::LeanObject,
    mut v_x_6280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6281_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_6277_, v_x_6279_);
    return v___x_6281_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(
    mut v_00_u03b1_6282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6283_: *mut crate::leanh::LeanObject,
    mut v_x_6284_: *mut crate::leanh::LeanObject,
    mut v_x_6285_: *mut crate::leanh::LeanObject,
    mut v_x_6286_: *mut crate::leanh::LeanObject,
    mut v_x_6287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6288_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(
        v_00_u03b1_6282_,
        v_00_u03b2_6283_,
        v_x_6284_,
        v_x_6285_,
        v_x_6286_,
        v_x_6287_,
    );
    crate::leanh::lean_dec(v_x_6284_);
    return v_res_6288_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(
    mut v_x_6289_: *mut crate::leanh::LeanObject,
    mut v_x_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: u8 = 0;
    let mut v___x_6304_: u8 = 0;
    let mut v_size_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6289_) == 0 {
                    v_k_6291_ = crate::leanh::lean_ctor_get(v_x_6289_, 1);
                    v_v_6292_ = crate::leanh::lean_ctor_get(v_x_6289_, 2);
                    v_l_6293_ = crate::leanh::lean_ctor_get(v_x_6289_, 3);
                    v_r_6294_ = crate::leanh::lean_ctor_get(v_x_6289_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6293_) == 0 {
                        v_size_6310_ = crate::leanh::lean_ctor_get(v_l_6293_, 0);
                        v___y_6302_ = v_size_6310_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6311_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6302_ = v___x_6311_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6290_);
                    v___x_6312_ = crate::leanh::lean_box(0);
                    return v___x_6312_;
                }
            }
            1 => {
                v___x_6297_ = lean_nat_sub(v_x_6290_, v___y_6296_);
                crate::leanh::lean_dec(v_x_6290_);
                v___x_6298_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6299_ = lean_nat_sub(v___x_6297_, v___x_6298_);
                crate::leanh::lean_dec(v___x_6297_);
                v_x_6289_ = v_r_6294_;
                v_x_6290_ = v___x_6299_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6303_ = lean_nat_dec_lt(v_x_6290_, v___y_6302_);
                if v___x_6303_ == 0 {
                    v___x_6304_ = lean_nat_dec_eq(v_x_6290_, v___y_6302_);
                    if v___x_6304_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6293_) == 0 {
                            v_size_6305_ = crate::leanh::lean_ctor_get(v_l_6293_, 0);
                            v___y_6296_ = v_size_6305_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6306_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6296_ = v___x_6306_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6290_);
                        crate::leanh::lean_inc(v_v_6292_);
                        crate::leanh::lean_inc(v_k_6291_);
                        v___x_6307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6307_, 0, v_k_6291_);
                        crate::leanh::lean_ctor_set(v___x_6307_, 1, v_v_6292_);
                        v___x_6308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6308_, 0, v___x_6307_);
                        return v___x_6308_;
                    }
                } else {
                    v_x_6289_ = v_l_6293_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(
    mut v_x_6313_: *mut crate::leanh::LeanObject,
    mut v_x_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6315_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_6313_, v_x_6314_);
    crate::leanh::lean_dec(v_x_6313_);
    return v_res_6315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(
    mut v_00_u03b1_6316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6317_: *mut crate::leanh::LeanObject,
    mut v_x_6318_: *mut crate::leanh::LeanObject,
    mut v_x_6319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6320_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_6318_, v_x_6319_);
    return v___x_6320_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_6321_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6322_: *mut crate::leanh::LeanObject,
    mut v_x_6323_: *mut crate::leanh::LeanObject,
    mut v_x_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(
        v_00_u03b1_6321_,
        v_00_u03b2_6322_,
        v_x_6323_,
        v_x_6324_,
    );
    crate::leanh::lean_dec(v_x_6323_);
    return v_res_6325_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1;
    v___x_6329_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6330_ = crate::leanh::lean_unsigned_to_nat(467);
    v___x_6331_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0;
    v___x_6332_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_6333_ = l_mkPanicMessageWithDecl(
        v___x_6332_,
        v___x_6331_,
        v___x_6330_,
        v___x_6329_,
        v___x_6328_,
    );
    return v___x_6333_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(
    mut v_inst_6334_: *mut crate::leanh::LeanObject,
    mut v_x_6335_: *mut crate::leanh::LeanObject,
    mut v_x_6336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: u8 = 0;
    let mut v_size_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6335_) == 0 {
                    v_k_6337_ = crate::leanh::lean_ctor_get(v_x_6335_, 1);
                    v_v_6338_ = crate::leanh::lean_ctor_get(v_x_6335_, 2);
                    v_l_6339_ = crate::leanh::lean_ctor_get(v_x_6335_, 3);
                    v_r_6340_ = crate::leanh::lean_ctor_get(v_x_6335_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6339_) == 0 {
                        v_size_6355_ = crate::leanh::lean_ctor_get(v_l_6339_, 0);
                        v___y_6348_ = v_size_6355_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6356_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6348_ = v___x_6356_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6336_);
                    v___x_6357_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2,
                    );
                    v___x_6358_ = l_panic___redArg(v_inst_6334_, v___x_6357_);
                    return v___x_6358_;
                }
            }
            1 => {
                v___x_6343_ = lean_nat_sub(v_x_6336_, v___y_6342_);
                crate::leanh::lean_dec(v_x_6336_);
                v___x_6344_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6345_ = lean_nat_sub(v___x_6343_, v___x_6344_);
                crate::leanh::lean_dec(v___x_6343_);
                v_x_6335_ = v_r_6340_;
                v_x_6336_ = v___x_6345_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6349_ = lean_nat_dec_lt(v_x_6336_, v___y_6348_);
                if v___x_6349_ == 0 {
                    v___x_6350_ = lean_nat_dec_eq(v_x_6336_, v___y_6348_);
                    if v___x_6350_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6339_) == 0 {
                            v_size_6351_ = crate::leanh::lean_ctor_get(v_l_6339_, 0);
                            v___y_6342_ = v_size_6351_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6352_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6342_ = v___x_6352_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6336_);
                        crate::leanh::lean_inc(v_v_6338_);
                        crate::leanh::lean_inc(v_k_6337_);
                        v___x_6353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6353_, 0, v_k_6337_);
                        crate::leanh::lean_ctor_set(v___x_6353_, 1, v_v_6338_);
                        return v___x_6353_;
                    }
                } else {
                    v_x_6335_ = v_l_6339_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(
    mut v_inst_6359_: *mut crate::leanh::LeanObject,
    mut v_x_6360_: *mut crate::leanh::LeanObject,
    mut v_x_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6362_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_6359_, v_x_6360_, v_x_6361_);
    crate::leanh::lean_dec(v_x_6360_);
    crate::leanh::lean_dec_ref(v_inst_6359_);
    return v_res_6362_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(
    mut v_00_u03b1_6363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6364_: *mut crate::leanh::LeanObject,
    mut v_inst_6365_: *mut crate::leanh::LeanObject,
    mut v_x_6366_: *mut crate::leanh::LeanObject,
    mut v_x_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6368_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_6365_, v_x_6366_, v_x_6367_);
    return v___x_6368_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(
    mut v_00_u03b1_6369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6370_: *mut crate::leanh::LeanObject,
    mut v_inst_6371_: *mut crate::leanh::LeanObject,
    mut v_x_6372_: *mut crate::leanh::LeanObject,
    mut v_x_6373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6374_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(
        v_00_u03b1_6369_,
        v_00_u03b2_6370_,
        v_inst_6371_,
        v_x_6372_,
        v_x_6373_,
    );
    crate::leanh::lean_dec(v_x_6372_);
    crate::leanh::lean_dec_ref(v_inst_6371_);
    return v_res_6374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(
    mut v_x_6375_: *mut crate::leanh::LeanObject,
    mut v_x_6376_: *mut crate::leanh::LeanObject,
    mut v_x_6377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: u8 = 0;
    let mut v___x_6391_: u8 = 0;
    let mut v_size_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6375_) == 0 {
                    v_k_6378_ = crate::leanh::lean_ctor_get(v_x_6375_, 1);
                    v_v_6379_ = crate::leanh::lean_ctor_get(v_x_6375_, 2);
                    v_l_6380_ = crate::leanh::lean_ctor_get(v_x_6375_, 3);
                    v_r_6381_ = crate::leanh::lean_ctor_get(v_x_6375_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6380_) == 0 {
                        v_size_6396_ = crate::leanh::lean_ctor_get(v_l_6380_, 0);
                        v___y_6389_ = v_size_6396_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6397_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6389_ = v___x_6397_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6376_);
                    crate::leanh::lean_inc_ref(v_x_6377_);
                    return v_x_6377_;
                }
            }
            1 => {
                v___x_6384_ = lean_nat_sub(v_x_6376_, v___y_6383_);
                crate::leanh::lean_dec(v_x_6376_);
                v___x_6385_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6386_ = lean_nat_sub(v___x_6384_, v___x_6385_);
                crate::leanh::lean_dec(v___x_6384_);
                v_x_6375_ = v_r_6381_;
                v_x_6376_ = v___x_6386_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6390_ = lean_nat_dec_lt(v_x_6376_, v___y_6389_);
                if v___x_6390_ == 0 {
                    v___x_6391_ = lean_nat_dec_eq(v_x_6376_, v___y_6389_);
                    if v___x_6391_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6380_) == 0 {
                            v_size_6392_ = crate::leanh::lean_ctor_get(v_l_6380_, 0);
                            v___y_6383_ = v_size_6392_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6393_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6383_ = v___x_6393_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6376_);
                        crate::leanh::lean_inc(v_v_6379_);
                        crate::leanh::lean_inc(v_k_6378_);
                        v___x_6394_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6394_, 0, v_k_6378_);
                        crate::leanh::lean_ctor_set(v___x_6394_, 1, v_v_6379_);
                        return v___x_6394_;
                    }
                } else {
                    v_x_6375_ = v_l_6380_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(
    mut v_x_6398_: *mut crate::leanh::LeanObject,
    mut v_x_6399_: *mut crate::leanh::LeanObject,
    mut v_x_6400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6401_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_6398_, v_x_6399_, v_x_6400_);
    crate::leanh::lean_dec_ref(v_x_6400_);
    crate::leanh::lean_dec(v_x_6398_);
    return v_res_6401_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdxD(
    mut v_00_u03b1_6402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6403_: *mut crate::leanh::LeanObject,
    mut v_x_6404_: *mut crate::leanh::LeanObject,
    mut v_x_6405_: *mut crate::leanh::LeanObject,
    mut v_x_6406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6407_ =
        l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_6404_, v_x_6405_, v_x_6406_);
    return v___x_6407_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(
    mut v_00_u03b1_6408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6409_: *mut crate::leanh::LeanObject,
    mut v_x_6410_: *mut crate::leanh::LeanObject,
    mut v_x_6411_: *mut crate::leanh::LeanObject,
    mut v_x_6412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6413_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(
        v_00_u03b1_6408_,
        v_00_u03b2_6409_,
        v_x_6410_,
        v_x_6411_,
        v_x_6412_,
    );
    crate::leanh::lean_dec_ref(v_x_6412_);
    crate::leanh::lean_dec(v_x_6410_);
    return v_res_6413_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(
    mut v_x_6414_: *mut crate::leanh::LeanObject,
    mut v_x_6415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: u8 = 0;
    let mut v___x_6428_: u8 = 0;
    let mut v_size_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_6416_ = crate::leanh::lean_ctor_get(v_x_6414_, 1);
                v_l_6417_ = crate::leanh::lean_ctor_get(v_x_6414_, 3);
                v_r_6418_ = crate::leanh::lean_ctor_get(v_x_6414_, 4);
                if crate::leanh::lean_obj_tag(v_l_6417_) == 0 {
                    v_size_6432_ = crate::leanh::lean_ctor_get(v_l_6417_, 0);
                    v___y_6426_ = v_size_6432_;
                    state = 2;
                    continue;
                } else {
                    v___x_6433_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6426_ = v___x_6433_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6421_ = lean_nat_sub(v_x_6415_, v___y_6420_);
                crate::leanh::lean_dec(v_x_6415_);
                v___x_6422_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6423_ = lean_nat_sub(v___x_6421_, v___x_6422_);
                crate::leanh::lean_dec(v___x_6421_);
                v_x_6414_ = v_r_6418_;
                v_x_6415_ = v___x_6423_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6427_ = lean_nat_dec_lt(v_x_6415_, v___y_6426_);
                if v___x_6427_ == 0 {
                    v___x_6428_ = lean_nat_dec_eq(v_x_6415_, v___y_6426_);
                    if v___x_6428_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6417_) == 0 {
                            v_size_6429_ = crate::leanh::lean_ctor_get(v_l_6417_, 0);
                            v___y_6420_ = v_size_6429_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6430_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6420_ = v___x_6430_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6415_);
                        crate::leanh::lean_inc(v_k_6416_);
                        return v_k_6416_;
                    }
                } else {
                    v_x_6414_ = v_l_6417_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(
    mut v_x_6434_: *mut crate::leanh::LeanObject,
    mut v_x_6435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6436_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_6434_, v_x_6435_);
    crate::leanh::lean_dec(v_x_6434_);
    return v_res_6436_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx(
    mut v_00_u03b1_6437_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6438_: *mut crate::leanh::LeanObject,
    mut v_x_6439_: *mut crate::leanh::LeanObject,
    mut v_x_6440_: *mut crate::leanh::LeanObject,
    mut v_x_6441_: *mut crate::leanh::LeanObject,
    mut v_x_6442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6443_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_6439_, v_x_6441_);
    return v___x_6443_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(
    mut v_00_u03b1_6444_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6445_: *mut crate::leanh::LeanObject,
    mut v_x_6446_: *mut crate::leanh::LeanObject,
    mut v_x_6447_: *mut crate::leanh::LeanObject,
    mut v_x_6448_: *mut crate::leanh::LeanObject,
    mut v_x_6449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6450_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(
        v_00_u03b1_6444_,
        v_00_u03b2_6445_,
        v_x_6446_,
        v_x_6447_,
        v_x_6448_,
        v_x_6449_,
    );
    crate::leanh::lean_dec(v_x_6446_);
    return v_res_6450_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(
    mut v_x_6451_: *mut crate::leanh::LeanObject,
    mut v_x_6452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: u8 = 0;
    let mut v_size_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6451_) == 0 {
                    v_k_6453_ = crate::leanh::lean_ctor_get(v_x_6451_, 1);
                    v_l_6454_ = crate::leanh::lean_ctor_get(v_x_6451_, 3);
                    v_r_6455_ = crate::leanh::lean_ctor_get(v_x_6451_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6454_) == 0 {
                        v_size_6470_ = crate::leanh::lean_ctor_get(v_l_6454_, 0);
                        v___y_6463_ = v_size_6470_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6471_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6463_ = v___x_6471_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6452_);
                    v___x_6472_ = crate::leanh::lean_box(0);
                    return v___x_6472_;
                }
            }
            1 => {
                v___x_6458_ = lean_nat_sub(v_x_6452_, v___y_6457_);
                crate::leanh::lean_dec(v_x_6452_);
                v___x_6459_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6460_ = lean_nat_sub(v___x_6458_, v___x_6459_);
                crate::leanh::lean_dec(v___x_6458_);
                v_x_6451_ = v_r_6455_;
                v_x_6452_ = v___x_6460_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6464_ = lean_nat_dec_lt(v_x_6452_, v___y_6463_);
                if v___x_6464_ == 0 {
                    v___x_6465_ = lean_nat_dec_eq(v_x_6452_, v___y_6463_);
                    if v___x_6465_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6454_) == 0 {
                            v_size_6466_ = crate::leanh::lean_ctor_get(v_l_6454_, 0);
                            v___y_6457_ = v_size_6466_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6467_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6457_ = v___x_6467_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6452_);
                        crate::leanh::lean_inc(v_k_6453_);
                        v___x_6468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6468_, 0, v_k_6453_);
                        return v___x_6468_;
                    }
                } else {
                    v_x_6451_ = v_l_6454_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(
    mut v_x_6473_: *mut crate::leanh::LeanObject,
    mut v_x_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6475_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_6473_, v_x_6474_);
    crate::leanh::lean_dec(v_x_6473_);
    return v_res_6475_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(
    mut v_00_u03b1_6476_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6477_: *mut crate::leanh::LeanObject,
    mut v_x_6478_: *mut crate::leanh::LeanObject,
    mut v_x_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_6478_, v_x_6479_);
    return v___x_6480_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(
    mut v_00_u03b1_6481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6482_: *mut crate::leanh::LeanObject,
    mut v_x_6483_: *mut crate::leanh::LeanObject,
    mut v_x_6484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6485_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(
        v_00_u03b1_6481_,
        v_00_u03b2_6482_,
        v_x_6483_,
        v_x_6484_,
    );
    crate::leanh::lean_dec(v_x_6483_);
    return v_res_6485_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6487_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1;
    v___x_6488_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6489_ = crate::leanh::lean_unsigned_to_nat(503);
    v___x_6490_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0;
    v___x_6491_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_6492_ = l_mkPanicMessageWithDecl(
        v___x_6491_,
        v___x_6490_,
        v___x_6489_,
        v___x_6488_,
        v___x_6487_,
    );
    return v___x_6492_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(
    mut v_inst_6493_: *mut crate::leanh::LeanObject,
    mut v_x_6494_: *mut crate::leanh::LeanObject,
    mut v_x_6495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: u8 = 0;
    let mut v___x_6508_: u8 = 0;
    let mut v_size_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6494_) == 0 {
                    v_k_6496_ = crate::leanh::lean_ctor_get(v_x_6494_, 1);
                    v_l_6497_ = crate::leanh::lean_ctor_get(v_x_6494_, 3);
                    v_r_6498_ = crate::leanh::lean_ctor_get(v_x_6494_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6497_) == 0 {
                        v_size_6512_ = crate::leanh::lean_ctor_get(v_l_6497_, 0);
                        v___y_6506_ = v_size_6512_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6513_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6506_ = v___x_6513_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6495_);
                    v___x_6514_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1,
                    );
                    v___x_6515_ = l_panic___redArg(v_inst_6493_, v___x_6514_);
                    return v___x_6515_;
                }
            }
            1 => {
                v___x_6501_ = lean_nat_sub(v_x_6495_, v___y_6500_);
                crate::leanh::lean_dec(v_x_6495_);
                v___x_6502_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6503_ = lean_nat_sub(v___x_6501_, v___x_6502_);
                crate::leanh::lean_dec(v___x_6501_);
                v_x_6494_ = v_r_6498_;
                v_x_6495_ = v___x_6503_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6507_ = lean_nat_dec_lt(v_x_6495_, v___y_6506_);
                if v___x_6507_ == 0 {
                    v___x_6508_ = lean_nat_dec_eq(v_x_6495_, v___y_6506_);
                    if v___x_6508_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6497_) == 0 {
                            v_size_6509_ = crate::leanh::lean_ctor_get(v_l_6497_, 0);
                            v___y_6500_ = v_size_6509_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6510_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6500_ = v___x_6510_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6495_);
                        crate::leanh::lean_inc(v_k_6496_);
                        return v_k_6496_;
                    }
                } else {
                    v_x_6494_ = v_l_6497_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(
    mut v_inst_6516_: *mut crate::leanh::LeanObject,
    mut v_x_6517_: *mut crate::leanh::LeanObject,
    mut v_x_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6519_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_6516_, v_x_6517_, v_x_6518_);
    crate::leanh::lean_dec(v_x_6517_);
    crate::leanh::lean_dec(v_inst_6516_);
    return v_res_6519_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(
    mut v_00_u03b1_6520_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6521_: *mut crate::leanh::LeanObject,
    mut v_inst_6522_: *mut crate::leanh::LeanObject,
    mut v_x_6523_: *mut crate::leanh::LeanObject,
    mut v_x_6524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6525_ =
        l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_6522_, v_x_6523_, v_x_6524_);
    return v___x_6525_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(
    mut v_00_u03b1_6526_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6527_: *mut crate::leanh::LeanObject,
    mut v_inst_6528_: *mut crate::leanh::LeanObject,
    mut v_x_6529_: *mut crate::leanh::LeanObject,
    mut v_x_6530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6531_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(
        v_00_u03b1_6526_,
        v_00_u03b2_6527_,
        v_inst_6528_,
        v_x_6529_,
        v_x_6530_,
    );
    crate::leanh::lean_dec(v_x_6529_);
    crate::leanh::lean_dec(v_inst_6528_);
    return v_res_6531_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(
    mut v_x_6532_: *mut crate::leanh::LeanObject,
    mut v_x_6533_: *mut crate::leanh::LeanObject,
    mut v_x_6534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: u8 = 0;
    let mut v___x_6547_: u8 = 0;
    let mut v_size_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6532_) == 0 {
                    v_k_6535_ = crate::leanh::lean_ctor_get(v_x_6532_, 1);
                    v_l_6536_ = crate::leanh::lean_ctor_get(v_x_6532_, 3);
                    v_r_6537_ = crate::leanh::lean_ctor_get(v_x_6532_, 4);
                    if crate::leanh::lean_obj_tag(v_l_6536_) == 0 {
                        v_size_6551_ = crate::leanh::lean_ctor_get(v_l_6536_, 0);
                        v___y_6545_ = v_size_6551_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6552_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_6545_ = v___x_6552_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_6533_);
                    crate::leanh::lean_inc(v_x_6534_);
                    return v_x_6534_;
                }
            }
            1 => {
                v___x_6540_ = lean_nat_sub(v_x_6533_, v___y_6539_);
                crate::leanh::lean_dec(v_x_6533_);
                v___x_6541_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6542_ = lean_nat_sub(v___x_6540_, v___x_6541_);
                crate::leanh::lean_dec(v___x_6540_);
                v_x_6532_ = v_r_6537_;
                v_x_6533_ = v___x_6542_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6546_ = lean_nat_dec_lt(v_x_6533_, v___y_6545_);
                if v___x_6546_ == 0 {
                    v___x_6547_ = lean_nat_dec_eq(v_x_6533_, v___y_6545_);
                    if v___x_6547_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_6536_) == 0 {
                            v_size_6548_ = crate::leanh::lean_ctor_get(v_l_6536_, 0);
                            v___y_6539_ = v_size_6548_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6549_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_6539_ = v___x_6549_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6533_);
                        crate::leanh::lean_inc(v_k_6535_);
                        return v_k_6535_;
                    }
                } else {
                    v_x_6532_ = v_l_6536_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(
    mut v_x_6553_: *mut crate::leanh::LeanObject,
    mut v_x_6554_: *mut crate::leanh::LeanObject,
    mut v_x_6555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6556_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_6553_, v_x_6554_, v_x_6555_);
    crate::leanh::lean_dec(v_x_6555_);
    crate::leanh::lean_dec(v_x_6553_);
    return v_res_6556_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdxD(
    mut v_00_u03b1_6557_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6558_: *mut crate::leanh::LeanObject,
    mut v_x_6559_: *mut crate::leanh::LeanObject,
    mut v_x_6560_: *mut crate::leanh::LeanObject,
    mut v_x_6561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6562_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_6559_, v_x_6560_, v_x_6561_);
    return v___x_6562_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(
    mut v_00_u03b1_6563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6564_: *mut crate::leanh::LeanObject,
    mut v_x_6565_: *mut crate::leanh::LeanObject,
    mut v_x_6566_: *mut crate::leanh::LeanObject,
    mut v_x_6567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6568_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(
        v_00_u03b1_6563_,
        v_00_u03b2_6564_,
        v_x_6565_,
        v_x_6566_,
        v_x_6567_,
    );
    crate::leanh::lean_dec(v_x_6567_);
    crate::leanh::lean_dec(v_x_6565_);
    return v_res_6568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
    mut v_inst_6569_: *mut crate::leanh::LeanObject,
    mut v_k_6570_: *mut crate::leanh::LeanObject,
    mut v_best_6571_: *mut crate::leanh::LeanObject,
    mut v_a_6572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: u8 = 0;
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6572_) == 0 {
                    v_k_6573_ = crate::leanh::lean_ctor_get(v_a_6572_, 1);
                    crate::leanh::lean_inc_n(v_k_6573_, 2);
                    v_v_6574_ = crate::leanh::lean_ctor_get(v_a_6572_, 2);
                    crate::leanh::lean_inc(v_v_6574_);
                    v_l_6575_ = crate::leanh::lean_ctor_get(v_a_6572_, 3);
                    crate::leanh::lean_inc(v_l_6575_);
                    v_r_6576_ = crate::leanh::lean_ctor_get(v_a_6572_, 4);
                    crate::leanh::lean_inc(v_r_6576_);
                    crate::leanh::lean_dec_ref_known(v_a_6572_, 5);
                    crate::leanh::lean_inc_ref(v_inst_6569_);
                    crate::leanh::lean_inc(v_k_6570_);
                    v___x_6577_ = crate::leanh::lean_apply_2(v_inst_6569_, v_k_6570_, v_k_6573_);
                    v___x_6578_ = (crate::leanh::lean_unbox(v___x_6577_) as u8);
                    match v___x_6578_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_6576_);
                            crate::leanh::lean_dec(v_best_6571_);
                            v___x_6579_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6579_, 0, v_k_6573_);
                            crate::leanh::lean_ctor_set(v___x_6579_, 1, v_v_6574_);
                            v___x_6580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6580_, 0, v___x_6579_);
                            v_best_6571_ = v___x_6580_;
                            v_a_6572_ = v_l_6575_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_6576_);
                            crate::leanh::lean_dec(v_l_6575_);
                            crate::leanh::lean_dec(v_best_6571_);
                            crate::leanh::lean_dec(v_k_6570_);
                            crate::leanh::lean_dec_ref(v_inst_6569_);
                            v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6582_, 0, v_k_6573_);
                            crate::leanh::lean_ctor_set(v___x_6582_, 1, v_v_6574_);
                            v___x_6583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6583_, 0, v___x_6582_);
                            return v___x_6583_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_6575_);
                            crate::leanh::lean_dec(v_v_6574_);
                            crate::leanh::lean_dec(v_k_6573_);
                            v_a_6572_ = v_r_6576_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6570_);
                    crate::leanh::lean_dec_ref(v_inst_6569_);
                    return v_best_6571_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(
    mut v_00_u03b1_6585_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6586_: *mut crate::leanh::LeanObject,
    mut v_inst_6587_: *mut crate::leanh::LeanObject,
    mut v_k_6588_: *mut crate::leanh::LeanObject,
    mut v_best_6589_: *mut crate::leanh::LeanObject,
    mut v_a_6590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6591_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6587_,
        v_k_6588_,
        v_best_6589_,
        v_a_6590_,
    );
    return v___x_6591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(
    mut v_inst_6592_: *mut crate::leanh::LeanObject,
    mut v_k_6593_: *mut crate::leanh::LeanObject,
    mut v_a_6594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6595_ = crate::leanh::lean_box(0);
    v___x_6596_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6592_,
        v_k_6593_,
        v___x_6595_,
        v_a_6594_,
    );
    return v___x_6596_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(
    mut v_00_u03b1_6597_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6598_: *mut crate::leanh::LeanObject,
    mut v_inst_6599_: *mut crate::leanh::LeanObject,
    mut v_k_6600_: *mut crate::leanh::LeanObject,
    mut v_a_6601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6602_ = crate::leanh::lean_box(0);
    v___x_6603_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6599_,
        v_k_6600_,
        v___x_6602_,
        v_a_6601_,
    );
    return v___x_6603_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
    mut v_inst_6604_: *mut crate::leanh::LeanObject,
    mut v_k_6605_: *mut crate::leanh::LeanObject,
    mut v_best_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: u8 = 0;
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6607_) == 0 {
                    v_k_6608_ = crate::leanh::lean_ctor_get(v_a_6607_, 1);
                    crate::leanh::lean_inc_n(v_k_6608_, 2);
                    v_v_6609_ = crate::leanh::lean_ctor_get(v_a_6607_, 2);
                    crate::leanh::lean_inc(v_v_6609_);
                    v_l_6610_ = crate::leanh::lean_ctor_get(v_a_6607_, 3);
                    crate::leanh::lean_inc(v_l_6610_);
                    v_r_6611_ = crate::leanh::lean_ctor_get(v_a_6607_, 4);
                    crate::leanh::lean_inc(v_r_6611_);
                    crate::leanh::lean_dec_ref_known(v_a_6607_, 5);
                    crate::leanh::lean_inc_ref(v_inst_6604_);
                    crate::leanh::lean_inc(v_k_6605_);
                    v___x_6612_ = crate::leanh::lean_apply_2(v_inst_6604_, v_k_6605_, v_k_6608_);
                    v___x_6613_ = (crate::leanh::lean_unbox(v___x_6612_) as u8);
                    if v___x_6613_ == 0 {
                        crate::leanh::lean_dec(v_r_6611_);
                        crate::leanh::lean_dec(v_best_6606_);
                        v___x_6614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6614_, 0, v_k_6608_);
                        crate::leanh::lean_ctor_set(v___x_6614_, 1, v_v_6609_);
                        v___x_6615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6615_, 0, v___x_6614_);
                        v_best_6606_ = v___x_6615_;
                        v_a_6607_ = v_l_6610_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_6610_);
                        crate::leanh::lean_dec(v_v_6609_);
                        crate::leanh::lean_dec(v_k_6608_);
                        v_a_6607_ = v_r_6611_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6605_);
                    crate::leanh::lean_dec_ref(v_inst_6604_);
                    return v_best_6606_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(
    mut v_00_u03b1_6618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6619_: *mut crate::leanh::LeanObject,
    mut v_inst_6620_: *mut crate::leanh::LeanObject,
    mut v_k_6621_: *mut crate::leanh::LeanObject,
    mut v_best_6622_: *mut crate::leanh::LeanObject,
    mut v_a_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6624_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6620_,
        v_k_6621_,
        v_best_6622_,
        v_a_6623_,
    );
    return v___x_6624_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(
    mut v_inst_6625_: *mut crate::leanh::LeanObject,
    mut v_k_6626_: *mut crate::leanh::LeanObject,
    mut v_a_6627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6628_ = crate::leanh::lean_box(0);
    v___x_6629_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6625_,
        v_k_6626_,
        v___x_6628_,
        v_a_6627_,
    );
    return v___x_6629_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(
    mut v_00_u03b1_6630_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6631_: *mut crate::leanh::LeanObject,
    mut v_inst_6632_: *mut crate::leanh::LeanObject,
    mut v_k_6633_: *mut crate::leanh::LeanObject,
    mut v_a_6634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6635_ = crate::leanh::lean_box(0);
    v___x_6636_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6632_,
        v_k_6633_,
        v___x_6635_,
        v_a_6634_,
    );
    return v___x_6636_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
    mut v_inst_6637_: *mut crate::leanh::LeanObject,
    mut v_k_6638_: *mut crate::leanh::LeanObject,
    mut v_best_6639_: *mut crate::leanh::LeanObject,
    mut v_a_6640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: u8 = 0;
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6640_) == 0 {
                    v_k_6641_ = crate::leanh::lean_ctor_get(v_a_6640_, 1);
                    crate::leanh::lean_inc_n(v_k_6641_, 2);
                    v_v_6642_ = crate::leanh::lean_ctor_get(v_a_6640_, 2);
                    crate::leanh::lean_inc(v_v_6642_);
                    v_l_6643_ = crate::leanh::lean_ctor_get(v_a_6640_, 3);
                    crate::leanh::lean_inc(v_l_6643_);
                    v_r_6644_ = crate::leanh::lean_ctor_get(v_a_6640_, 4);
                    crate::leanh::lean_inc(v_r_6644_);
                    crate::leanh::lean_dec_ref_known(v_a_6640_, 5);
                    crate::leanh::lean_inc_ref(v_inst_6637_);
                    crate::leanh::lean_inc(v_k_6638_);
                    v___x_6645_ = crate::leanh::lean_apply_2(v_inst_6637_, v_k_6638_, v_k_6641_);
                    v___x_6646_ = (crate::leanh::lean_unbox(v___x_6645_) as u8);
                    match v___x_6646_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_6644_);
                            crate::leanh::lean_dec(v_v_6642_);
                            crate::leanh::lean_dec(v_k_6641_);
                            v_a_6640_ = v_l_6643_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_6644_);
                            crate::leanh::lean_dec(v_l_6643_);
                            crate::leanh::lean_dec(v_best_6639_);
                            crate::leanh::lean_dec(v_k_6638_);
                            crate::leanh::lean_dec_ref(v_inst_6637_);
                            v___x_6648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6648_, 0, v_k_6641_);
                            crate::leanh::lean_ctor_set(v___x_6648_, 1, v_v_6642_);
                            v___x_6649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6649_, 0, v___x_6648_);
                            return v___x_6649_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_6643_);
                            crate::leanh::lean_dec(v_best_6639_);
                            v___x_6650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6650_, 0, v_k_6641_);
                            crate::leanh::lean_ctor_set(v___x_6650_, 1, v_v_6642_);
                            v___x_6651_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6651_, 0, v___x_6650_);
                            v_best_6639_ = v___x_6651_;
                            v_a_6640_ = v_r_6644_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6638_);
                    crate::leanh::lean_dec_ref(v_inst_6637_);
                    return v_best_6639_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(
    mut v_00_u03b1_6653_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6654_: *mut crate::leanh::LeanObject,
    mut v_inst_6655_: *mut crate::leanh::LeanObject,
    mut v_k_6656_: *mut crate::leanh::LeanObject,
    mut v_best_6657_: *mut crate::leanh::LeanObject,
    mut v_a_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6659_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6655_,
        v_k_6656_,
        v_best_6657_,
        v_a_6658_,
    );
    return v___x_6659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(
    mut v_inst_6660_: *mut crate::leanh::LeanObject,
    mut v_k_6661_: *mut crate::leanh::LeanObject,
    mut v_a_6662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6663_ = crate::leanh::lean_box(0);
    v___x_6664_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6660_,
        v_k_6661_,
        v___x_6663_,
        v_a_6662_,
    );
    return v___x_6664_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(
    mut v_00_u03b1_6665_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6666_: *mut crate::leanh::LeanObject,
    mut v_inst_6667_: *mut crate::leanh::LeanObject,
    mut v_k_6668_: *mut crate::leanh::LeanObject,
    mut v_a_6669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6670_ = crate::leanh::lean_box(0);
    v___x_6671_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6667_,
        v_k_6668_,
        v___x_6670_,
        v_a_6669_,
    );
    return v___x_6671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
    mut v_inst_6672_: *mut crate::leanh::LeanObject,
    mut v_k_6673_: *mut crate::leanh::LeanObject,
    mut v_best_6674_: *mut crate::leanh::LeanObject,
    mut v_a_6675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u8 = 0;
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6675_) == 0 {
                    v_k_6676_ = crate::leanh::lean_ctor_get(v_a_6675_, 1);
                    crate::leanh::lean_inc_n(v_k_6676_, 2);
                    v_v_6677_ = crate::leanh::lean_ctor_get(v_a_6675_, 2);
                    crate::leanh::lean_inc(v_v_6677_);
                    v_l_6678_ = crate::leanh::lean_ctor_get(v_a_6675_, 3);
                    crate::leanh::lean_inc(v_l_6678_);
                    v_r_6679_ = crate::leanh::lean_ctor_get(v_a_6675_, 4);
                    crate::leanh::lean_inc(v_r_6679_);
                    crate::leanh::lean_dec_ref_known(v_a_6675_, 5);
                    crate::leanh::lean_inc_ref(v_inst_6672_);
                    crate::leanh::lean_inc(v_k_6673_);
                    v___x_6680_ = crate::leanh::lean_apply_2(v_inst_6672_, v_k_6673_, v_k_6676_);
                    v___x_6681_ = (crate::leanh::lean_unbox(v___x_6680_) as u8);
                    if v___x_6681_ == 2 {
                        crate::leanh::lean_dec(v_l_6678_);
                        crate::leanh::lean_dec(v_best_6674_);
                        v___x_6682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6682_, 0, v_k_6676_);
                        crate::leanh::lean_ctor_set(v___x_6682_, 1, v_v_6677_);
                        v___x_6683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6683_, 0, v___x_6682_);
                        v_best_6674_ = v___x_6683_;
                        v_a_6675_ = v_r_6679_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_6679_);
                        crate::leanh::lean_dec(v_v_6677_);
                        crate::leanh::lean_dec(v_k_6676_);
                        v_a_6675_ = v_l_6678_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_6673_);
                    crate::leanh::lean_dec_ref(v_inst_6672_);
                    return v_best_6674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(
    mut v_00_u03b1_6686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6687_: *mut crate::leanh::LeanObject,
    mut v_inst_6688_: *mut crate::leanh::LeanObject,
    mut v_k_6689_: *mut crate::leanh::LeanObject,
    mut v_best_6690_: *mut crate::leanh::LeanObject,
    mut v_a_6691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6692_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6688_,
        v_k_6689_,
        v_best_6690_,
        v_a_6691_,
    );
    return v___x_6692_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(
    mut v_inst_6693_: *mut crate::leanh::LeanObject,
    mut v_k_6694_: *mut crate::leanh::LeanObject,
    mut v_a_6695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6696_ = crate::leanh::lean_box(0);
    v___x_6697_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6693_,
        v_k_6694_,
        v___x_6696_,
        v_a_6695_,
    );
    return v___x_6697_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(
    mut v_00_u03b1_6698_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6699_: *mut crate::leanh::LeanObject,
    mut v_inst_6700_: *mut crate::leanh::LeanObject,
    mut v_k_6701_: *mut crate::leanh::LeanObject,
    mut v_a_6702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6703_ = crate::leanh::lean_box(0);
    v___x_6704_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6700_,
        v_k_6701_,
        v___x_6703_,
        v_a_6702_,
    );
    return v___x_6704_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6708_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2;
    v___x_6709_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_6710_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_6711_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1;
    v___x_6712_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0;
    v___x_6713_ = l_mkPanicMessageWithDecl(
        v___x_6712_,
        v___x_6711_,
        v___x_6710_,
        v___x_6709_,
        v___x_6708_,
    );
    return v___x_6713_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(
    mut v_inst_6714_: *mut crate::leanh::LeanObject,
    mut v_inst_6715_: *mut crate::leanh::LeanObject,
    mut v_k_6716_: *mut crate::leanh::LeanObject,
    mut v_t_6717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6718_ = crate::leanh::lean_box(0);
    v___x_6719_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6714_,
        v_k_6716_,
        v___x_6718_,
        v_t_6717_,
    );
    if crate::leanh::lean_obj_tag(v___x_6719_) == 0 {
        let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6720_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6721_ = l_panic___redArg(v_inst_6715_, v___x_6720_);
        return v___x_6721_;
    } else {
        let mut v_val_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6722_ = crate::leanh::lean_ctor_get(v___x_6719_, 0);
        crate::leanh::lean_inc(v_val_6722_);
        crate::leanh::lean_dec_ref_known(v___x_6719_, 1);
        return v_val_6722_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(
    mut v_inst_6723_: *mut crate::leanh::LeanObject,
    mut v_inst_6724_: *mut crate::leanh::LeanObject,
    mut v_k_6725_: *mut crate::leanh::LeanObject,
    mut v_t_6726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6727_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(
        v_inst_6723_,
        v_inst_6724_,
        v_k_6725_,
        v_t_6726_,
    );
    crate::leanh::lean_dec_ref(v_inst_6724_);
    return v_res_6727_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(
    mut v_00_u03b1_6728_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6729_: *mut crate::leanh::LeanObject,
    mut v_inst_6730_: *mut crate::leanh::LeanObject,
    mut v_inst_6731_: *mut crate::leanh::LeanObject,
    mut v_k_6732_: *mut crate::leanh::LeanObject,
    mut v_t_6733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6734_ = crate::leanh::lean_box(0);
    v___x_6735_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6730_,
        v_k_6732_,
        v___x_6734_,
        v_t_6733_,
    );
    if crate::leanh::lean_obj_tag(v___x_6735_) == 0 {
        let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6736_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6737_ = l_panic___redArg(v_inst_6731_, v___x_6736_);
        return v___x_6737_;
    } else {
        let mut v_val_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6738_ = crate::leanh::lean_ctor_get(v___x_6735_, 0);
        crate::leanh::lean_inc(v_val_6738_);
        crate::leanh::lean_dec_ref_known(v___x_6735_, 1);
        return v_val_6738_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(
    mut v_00_u03b1_6739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6740_: *mut crate::leanh::LeanObject,
    mut v_inst_6741_: *mut crate::leanh::LeanObject,
    mut v_inst_6742_: *mut crate::leanh::LeanObject,
    mut v_k_6743_: *mut crate::leanh::LeanObject,
    mut v_t_6744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6745_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(
        v_00_u03b1_6739_,
        v_00_u03b2_6740_,
        v_inst_6741_,
        v_inst_6742_,
        v_k_6743_,
        v_t_6744_,
    );
    crate::leanh::lean_dec_ref(v_inst_6742_);
    return v_res_6745_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(
    mut v_inst_6746_: *mut crate::leanh::LeanObject,
    mut v_inst_6747_: *mut crate::leanh::LeanObject,
    mut v_k_6748_: *mut crate::leanh::LeanObject,
    mut v_t_6749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6750_ = crate::leanh::lean_box(0);
    v___x_6751_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6746_,
        v_k_6748_,
        v___x_6750_,
        v_t_6749_,
    );
    if crate::leanh::lean_obj_tag(v___x_6751_) == 0 {
        let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6752_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6753_ = l_panic___redArg(v_inst_6747_, v___x_6752_);
        return v___x_6753_;
    } else {
        let mut v_val_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6754_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
        crate::leanh::lean_inc(v_val_6754_);
        crate::leanh::lean_dec_ref_known(v___x_6751_, 1);
        return v_val_6754_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(
    mut v_inst_6755_: *mut crate::leanh::LeanObject,
    mut v_inst_6756_: *mut crate::leanh::LeanObject,
    mut v_k_6757_: *mut crate::leanh::LeanObject,
    mut v_t_6758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6759_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(
        v_inst_6755_,
        v_inst_6756_,
        v_k_6757_,
        v_t_6758_,
    );
    crate::leanh::lean_dec_ref(v_inst_6756_);
    return v_res_6759_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(
    mut v_00_u03b1_6760_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6761_: *mut crate::leanh::LeanObject,
    mut v_inst_6762_: *mut crate::leanh::LeanObject,
    mut v_inst_6763_: *mut crate::leanh::LeanObject,
    mut v_k_6764_: *mut crate::leanh::LeanObject,
    mut v_t_6765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6766_ = crate::leanh::lean_box(0);
    v___x_6767_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6762_,
        v_k_6764_,
        v___x_6766_,
        v_t_6765_,
    );
    if crate::leanh::lean_obj_tag(v___x_6767_) == 0 {
        let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6768_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6769_ = l_panic___redArg(v_inst_6763_, v___x_6768_);
        return v___x_6769_;
    } else {
        let mut v_val_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6770_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
        crate::leanh::lean_inc(v_val_6770_);
        crate::leanh::lean_dec_ref_known(v___x_6767_, 1);
        return v_val_6770_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(
    mut v_00_u03b1_6771_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6772_: *mut crate::leanh::LeanObject,
    mut v_inst_6773_: *mut crate::leanh::LeanObject,
    mut v_inst_6774_: *mut crate::leanh::LeanObject,
    mut v_k_6775_: *mut crate::leanh::LeanObject,
    mut v_t_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6777_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(
        v_00_u03b1_6771_,
        v_00_u03b2_6772_,
        v_inst_6773_,
        v_inst_6774_,
        v_k_6775_,
        v_t_6776_,
    );
    crate::leanh::lean_dec_ref(v_inst_6774_);
    return v_res_6777_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(
    mut v_inst_6778_: *mut crate::leanh::LeanObject,
    mut v_inst_6779_: *mut crate::leanh::LeanObject,
    mut v_k_6780_: *mut crate::leanh::LeanObject,
    mut v_t_6781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6782_ = crate::leanh::lean_box(0);
    v___x_6783_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6778_,
        v_k_6780_,
        v___x_6782_,
        v_t_6781_,
    );
    if crate::leanh::lean_obj_tag(v___x_6783_) == 0 {
        let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6784_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6785_ = l_panic___redArg(v_inst_6779_, v___x_6784_);
        return v___x_6785_;
    } else {
        let mut v_val_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6786_ = crate::leanh::lean_ctor_get(v___x_6783_, 0);
        crate::leanh::lean_inc(v_val_6786_);
        crate::leanh::lean_dec_ref_known(v___x_6783_, 1);
        return v_val_6786_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(
    mut v_inst_6787_: *mut crate::leanh::LeanObject,
    mut v_inst_6788_: *mut crate::leanh::LeanObject,
    mut v_k_6789_: *mut crate::leanh::LeanObject,
    mut v_t_6790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6791_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(
        v_inst_6787_,
        v_inst_6788_,
        v_k_6789_,
        v_t_6790_,
    );
    crate::leanh::lean_dec_ref(v_inst_6788_);
    return v_res_6791_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(
    mut v_00_u03b1_6792_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6793_: *mut crate::leanh::LeanObject,
    mut v_inst_6794_: *mut crate::leanh::LeanObject,
    mut v_inst_6795_: *mut crate::leanh::LeanObject,
    mut v_k_6796_: *mut crate::leanh::LeanObject,
    mut v_t_6797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6798_ = crate::leanh::lean_box(0);
    v___x_6799_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6794_,
        v_k_6796_,
        v___x_6798_,
        v_t_6797_,
    );
    if crate::leanh::lean_obj_tag(v___x_6799_) == 0 {
        let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6800_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6801_ = l_panic___redArg(v_inst_6795_, v___x_6800_);
        return v___x_6801_;
    } else {
        let mut v_val_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6802_ = crate::leanh::lean_ctor_get(v___x_6799_, 0);
        crate::leanh::lean_inc(v_val_6802_);
        crate::leanh::lean_dec_ref_known(v___x_6799_, 1);
        return v_val_6802_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(
    mut v_00_u03b1_6803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6804_: *mut crate::leanh::LeanObject,
    mut v_inst_6805_: *mut crate::leanh::LeanObject,
    mut v_inst_6806_: *mut crate::leanh::LeanObject,
    mut v_k_6807_: *mut crate::leanh::LeanObject,
    mut v_t_6808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6809_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(
        v_00_u03b1_6803_,
        v_00_u03b2_6804_,
        v_inst_6805_,
        v_inst_6806_,
        v_k_6807_,
        v_t_6808_,
    );
    crate::leanh::lean_dec_ref(v_inst_6806_);
    return v_res_6809_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(
    mut v_inst_6810_: *mut crate::leanh::LeanObject,
    mut v_inst_6811_: *mut crate::leanh::LeanObject,
    mut v_k_6812_: *mut crate::leanh::LeanObject,
    mut v_t_6813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6814_ = crate::leanh::lean_box(0);
    v___x_6815_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6810_,
        v_k_6812_,
        v___x_6814_,
        v_t_6813_,
    );
    if crate::leanh::lean_obj_tag(v___x_6815_) == 0 {
        let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6816_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6817_ = l_panic___redArg(v_inst_6811_, v___x_6816_);
        return v___x_6817_;
    } else {
        let mut v_val_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6818_ = crate::leanh::lean_ctor_get(v___x_6815_, 0);
        crate::leanh::lean_inc(v_val_6818_);
        crate::leanh::lean_dec_ref_known(v___x_6815_, 1);
        return v_val_6818_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(
    mut v_inst_6819_: *mut crate::leanh::LeanObject,
    mut v_inst_6820_: *mut crate::leanh::LeanObject,
    mut v_k_6821_: *mut crate::leanh::LeanObject,
    mut v_t_6822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6823_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(
        v_inst_6819_,
        v_inst_6820_,
        v_k_6821_,
        v_t_6822_,
    );
    crate::leanh::lean_dec_ref(v_inst_6820_);
    return v_res_6823_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(
    mut v_00_u03b1_6824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6825_: *mut crate::leanh::LeanObject,
    mut v_inst_6826_: *mut crate::leanh::LeanObject,
    mut v_inst_6827_: *mut crate::leanh::LeanObject,
    mut v_k_6828_: *mut crate::leanh::LeanObject,
    mut v_t_6829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6830_ = crate::leanh::lean_box(0);
    v___x_6831_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6826_,
        v_k_6828_,
        v___x_6830_,
        v_t_6829_,
    );
    if crate::leanh::lean_obj_tag(v___x_6831_) == 0 {
        let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6832_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_6833_ = l_panic___redArg(v_inst_6827_, v___x_6832_);
        return v___x_6833_;
    } else {
        let mut v_val_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6834_ = crate::leanh::lean_ctor_get(v___x_6831_, 0);
        crate::leanh::lean_inc(v_val_6834_);
        crate::leanh::lean_dec_ref_known(v___x_6831_, 1);
        return v_val_6834_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(
    mut v_00_u03b1_6835_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6836_: *mut crate::leanh::LeanObject,
    mut v_inst_6837_: *mut crate::leanh::LeanObject,
    mut v_inst_6838_: *mut crate::leanh::LeanObject,
    mut v_k_6839_: *mut crate::leanh::LeanObject,
    mut v_t_6840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6841_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(
        v_00_u03b1_6835_,
        v_00_u03b2_6836_,
        v_inst_6837_,
        v_inst_6838_,
        v_k_6839_,
        v_t_6840_,
    );
    crate::leanh::lean_dec_ref(v_inst_6838_);
    return v_res_6841_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(
    mut v_inst_6842_: *mut crate::leanh::LeanObject,
    mut v_k_6843_: *mut crate::leanh::LeanObject,
    mut v_t_6844_: *mut crate::leanh::LeanObject,
    mut v_fallback_6845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6846_ = crate::leanh::lean_box(0);
    v___x_6847_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6842_,
        v_k_6843_,
        v___x_6846_,
        v_t_6844_,
    );
    if crate::leanh::lean_obj_tag(v___x_6847_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6845_);
        return v_fallback_6845_;
    } else {
        let mut v_val_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6848_ = crate::leanh::lean_ctor_get(v___x_6847_, 0);
        crate::leanh::lean_inc(v_val_6848_);
        crate::leanh::lean_dec_ref_known(v___x_6847_, 1);
        return v_val_6848_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(
    mut v_inst_6849_: *mut crate::leanh::LeanObject,
    mut v_k_6850_: *mut crate::leanh::LeanObject,
    mut v_t_6851_: *mut crate::leanh::LeanObject,
    mut v_fallback_6852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6853_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(
        v_inst_6849_,
        v_k_6850_,
        v_t_6851_,
        v_fallback_6852_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6852_);
    return v_res_6853_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGED(
    mut v_00_u03b1_6854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6855_: *mut crate::leanh::LeanObject,
    mut v_inst_6856_: *mut crate::leanh::LeanObject,
    mut v_k_6857_: *mut crate::leanh::LeanObject,
    mut v_t_6858_: *mut crate::leanh::LeanObject,
    mut v_fallback_6859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6860_ = crate::leanh::lean_box(0);
    v___x_6861_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
        v_inst_6856_,
        v_k_6857_,
        v___x_6860_,
        v_t_6858_,
    );
    if crate::leanh::lean_obj_tag(v___x_6861_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6859_);
        return v_fallback_6859_;
    } else {
        let mut v_val_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6862_ = crate::leanh::lean_ctor_get(v___x_6861_, 0);
        crate::leanh::lean_inc(v_val_6862_);
        crate::leanh::lean_dec_ref_known(v___x_6861_, 1);
        return v_val_6862_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(
    mut v_00_u03b1_6863_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6864_: *mut crate::leanh::LeanObject,
    mut v_inst_6865_: *mut crate::leanh::LeanObject,
    mut v_k_6866_: *mut crate::leanh::LeanObject,
    mut v_t_6867_: *mut crate::leanh::LeanObject,
    mut v_fallback_6868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6869_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(
        v_00_u03b1_6863_,
        v_00_u03b2_6864_,
        v_inst_6865_,
        v_k_6866_,
        v_t_6867_,
        v_fallback_6868_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6868_);
    return v_res_6869_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(
    mut v_inst_6870_: *mut crate::leanh::LeanObject,
    mut v_k_6871_: *mut crate::leanh::LeanObject,
    mut v_t_6872_: *mut crate::leanh::LeanObject,
    mut v_fallback_6873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6874_ = crate::leanh::lean_box(0);
    v___x_6875_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6870_,
        v_k_6871_,
        v___x_6874_,
        v_t_6872_,
    );
    if crate::leanh::lean_obj_tag(v___x_6875_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6873_);
        return v_fallback_6873_;
    } else {
        let mut v_val_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6876_ = crate::leanh::lean_ctor_get(v___x_6875_, 0);
        crate::leanh::lean_inc(v_val_6876_);
        crate::leanh::lean_dec_ref_known(v___x_6875_, 1);
        return v_val_6876_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(
    mut v_inst_6877_: *mut crate::leanh::LeanObject,
    mut v_k_6878_: *mut crate::leanh::LeanObject,
    mut v_t_6879_: *mut crate::leanh::LeanObject,
    mut v_fallback_6880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6881_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(
        v_inst_6877_,
        v_k_6878_,
        v_t_6879_,
        v_fallback_6880_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6880_);
    return v_res_6881_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGTD(
    mut v_00_u03b1_6882_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6883_: *mut crate::leanh::LeanObject,
    mut v_inst_6884_: *mut crate::leanh::LeanObject,
    mut v_k_6885_: *mut crate::leanh::LeanObject,
    mut v_t_6886_: *mut crate::leanh::LeanObject,
    mut v_fallback_6887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6888_ = crate::leanh::lean_box(0);
    v___x_6889_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
        v_inst_6884_,
        v_k_6885_,
        v___x_6888_,
        v_t_6886_,
    );
    if crate::leanh::lean_obj_tag(v___x_6889_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6887_);
        return v_fallback_6887_;
    } else {
        let mut v_val_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6890_ = crate::leanh::lean_ctor_get(v___x_6889_, 0);
        crate::leanh::lean_inc(v_val_6890_);
        crate::leanh::lean_dec_ref_known(v___x_6889_, 1);
        return v_val_6890_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(
    mut v_00_u03b1_6891_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6892_: *mut crate::leanh::LeanObject,
    mut v_inst_6893_: *mut crate::leanh::LeanObject,
    mut v_k_6894_: *mut crate::leanh::LeanObject,
    mut v_t_6895_: *mut crate::leanh::LeanObject,
    mut v_fallback_6896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6897_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(
        v_00_u03b1_6891_,
        v_00_u03b2_6892_,
        v_inst_6893_,
        v_k_6894_,
        v_t_6895_,
        v_fallback_6896_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6896_);
    return v_res_6897_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(
    mut v_inst_6898_: *mut crate::leanh::LeanObject,
    mut v_k_6899_: *mut crate::leanh::LeanObject,
    mut v_t_6900_: *mut crate::leanh::LeanObject,
    mut v_fallback_6901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6902_ = crate::leanh::lean_box(0);
    v___x_6903_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6898_,
        v_k_6899_,
        v___x_6902_,
        v_t_6900_,
    );
    if crate::leanh::lean_obj_tag(v___x_6903_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6901_);
        return v_fallback_6901_;
    } else {
        let mut v_val_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6904_ = crate::leanh::lean_ctor_get(v___x_6903_, 0);
        crate::leanh::lean_inc(v_val_6904_);
        crate::leanh::lean_dec_ref_known(v___x_6903_, 1);
        return v_val_6904_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(
    mut v_inst_6905_: *mut crate::leanh::LeanObject,
    mut v_k_6906_: *mut crate::leanh::LeanObject,
    mut v_t_6907_: *mut crate::leanh::LeanObject,
    mut v_fallback_6908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6909_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(
        v_inst_6905_,
        v_k_6906_,
        v_t_6907_,
        v_fallback_6908_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6908_);
    return v_res_6909_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLED(
    mut v_00_u03b1_6910_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6911_: *mut crate::leanh::LeanObject,
    mut v_inst_6912_: *mut crate::leanh::LeanObject,
    mut v_k_6913_: *mut crate::leanh::LeanObject,
    mut v_t_6914_: *mut crate::leanh::LeanObject,
    mut v_fallback_6915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6916_ = crate::leanh::lean_box(0);
    v___x_6917_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
        v_inst_6912_,
        v_k_6913_,
        v___x_6916_,
        v_t_6914_,
    );
    if crate::leanh::lean_obj_tag(v___x_6917_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6915_);
        return v_fallback_6915_;
    } else {
        let mut v_val_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6918_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
        crate::leanh::lean_inc(v_val_6918_);
        crate::leanh::lean_dec_ref_known(v___x_6917_, 1);
        return v_val_6918_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(
    mut v_00_u03b1_6919_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6920_: *mut crate::leanh::LeanObject,
    mut v_inst_6921_: *mut crate::leanh::LeanObject,
    mut v_k_6922_: *mut crate::leanh::LeanObject,
    mut v_t_6923_: *mut crate::leanh::LeanObject,
    mut v_fallback_6924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6925_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(
        v_00_u03b1_6919_,
        v_00_u03b2_6920_,
        v_inst_6921_,
        v_k_6922_,
        v_t_6923_,
        v_fallback_6924_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6924_);
    return v_res_6925_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(
    mut v_inst_6926_: *mut crate::leanh::LeanObject,
    mut v_k_6927_: *mut crate::leanh::LeanObject,
    mut v_t_6928_: *mut crate::leanh::LeanObject,
    mut v_fallback_6929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6930_ = crate::leanh::lean_box(0);
    v___x_6931_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6926_,
        v_k_6927_,
        v___x_6930_,
        v_t_6928_,
    );
    if crate::leanh::lean_obj_tag(v___x_6931_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6929_);
        return v_fallback_6929_;
    } else {
        let mut v_val_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6932_ = crate::leanh::lean_ctor_get(v___x_6931_, 0);
        crate::leanh::lean_inc(v_val_6932_);
        crate::leanh::lean_dec_ref_known(v___x_6931_, 1);
        return v_val_6932_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(
    mut v_inst_6933_: *mut crate::leanh::LeanObject,
    mut v_k_6934_: *mut crate::leanh::LeanObject,
    mut v_t_6935_: *mut crate::leanh::LeanObject,
    mut v_fallback_6936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6937_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(
        v_inst_6933_,
        v_k_6934_,
        v_t_6935_,
        v_fallback_6936_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6936_);
    return v_res_6937_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLTD(
    mut v_00_u03b1_6938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6939_: *mut crate::leanh::LeanObject,
    mut v_inst_6940_: *mut crate::leanh::LeanObject,
    mut v_k_6941_: *mut crate::leanh::LeanObject,
    mut v_t_6942_: *mut crate::leanh::LeanObject,
    mut v_fallback_6943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6944_ = crate::leanh::lean_box(0);
    v___x_6945_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
        v_inst_6940_,
        v_k_6941_,
        v___x_6944_,
        v_t_6942_,
    );
    if crate::leanh::lean_obj_tag(v___x_6945_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_6943_);
        return v_fallback_6943_;
    } else {
        let mut v_val_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6946_ = crate::leanh::lean_ctor_get(v___x_6945_, 0);
        crate::leanh::lean_inc(v_val_6946_);
        crate::leanh::lean_dec_ref_known(v___x_6945_, 1);
        return v_val_6946_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(
    mut v_00_u03b1_6947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6948_: *mut crate::leanh::LeanObject,
    mut v_inst_6949_: *mut crate::leanh::LeanObject,
    mut v_k_6950_: *mut crate::leanh::LeanObject,
    mut v_t_6951_: *mut crate::leanh::LeanObject,
    mut v_fallback_6952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6953_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(
        v_00_u03b1_6947_,
        v_00_u03b2_6948_,
        v_inst_6949_,
        v_k_6950_,
        v_t_6951_,
        v_fallback_6952_,
    );
    crate::leanh::lean_dec_ref(v_fallback_6952_);
    return v_res_6953_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(
    mut v_inst_6954_: *mut crate::leanh::LeanObject,
    mut v_k_6955_: *mut crate::leanh::LeanObject,
    mut v_x_6956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: u8 = 0;
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_6957_ = crate::leanh::lean_ctor_get(v_x_6956_, 1);
                crate::leanh::lean_inc_n(v_k_6957_, 2);
                v_v_6958_ = crate::leanh::lean_ctor_get(v_x_6956_, 2);
                crate::leanh::lean_inc(v_v_6958_);
                v_l_6959_ = crate::leanh::lean_ctor_get(v_x_6956_, 3);
                crate::leanh::lean_inc(v_l_6959_);
                v_r_6960_ = crate::leanh::lean_ctor_get(v_x_6956_, 4);
                crate::leanh::lean_inc(v_r_6960_);
                crate::leanh::lean_dec(v_x_6956_);
                crate::leanh::lean_inc_ref(v_inst_6954_);
                crate::leanh::lean_inc(v_k_6955_);
                v___x_6961_ = crate::leanh::lean_apply_2(v_inst_6954_, v_k_6955_, v_k_6957_);
                v___x_6962_ = (crate::leanh::lean_unbox(v___x_6961_) as u8);
                match v___x_6962_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_6960_);
                        v___x_6963_ = crate::leanh::lean_box(0);
                        v___x_6964_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(
                            v_inst_6954_,
                            v_k_6955_,
                            v___x_6963_,
                            v_l_6959_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6964_) == 0 {
                            v___x_6965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6965_, 0, v_k_6957_);
                            crate::leanh::lean_ctor_set(v___x_6965_, 1, v_v_6958_);
                            return v___x_6965_;
                        } else {
                            crate::leanh::lean_dec(v_v_6958_);
                            crate::leanh::lean_dec(v_k_6957_);
                            v_val_6966_ = crate::leanh::lean_ctor_get(v___x_6964_, 0);
                            crate::leanh::lean_inc(v_val_6966_);
                            crate::leanh::lean_dec_ref_known(v___x_6964_, 1);
                            return v_val_6966_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_6960_);
                        crate::leanh::lean_dec(v_l_6959_);
                        crate::leanh::lean_dec(v_k_6955_);
                        crate::leanh::lean_dec_ref(v_inst_6954_);
                        v___x_6967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6967_, 0, v_k_6957_);
                        crate::leanh::lean_ctor_set(v___x_6967_, 1, v_v_6958_);
                        return v___x_6967_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_6959_);
                        crate::leanh::lean_dec(v_v_6958_);
                        crate::leanh::lean_dec(v_k_6957_);
                        v_x_6956_ = v_r_6960_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGE(
    mut v_00_u03b1_6969_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6970_: *mut crate::leanh::LeanObject,
    mut v_inst_6971_: *mut crate::leanh::LeanObject,
    mut v_inst_6972_: *mut crate::leanh::LeanObject,
    mut v_k_6973_: *mut crate::leanh::LeanObject,
    mut v_x_6974_: *mut crate::leanh::LeanObject,
    mut v_x_6975_: *mut crate::leanh::LeanObject,
    mut v_x_6976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6977_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_6971_, v_k_6973_, v_x_6974_);
    return v___x_6977_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(
    mut v_inst_6978_: *mut crate::leanh::LeanObject,
    mut v_k_6979_: *mut crate::leanh::LeanObject,
    mut v_x_6980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6987_: u8 = 0;
    let mut v___x_6988_: u8 = 0;
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_6981_ = crate::leanh::lean_ctor_get(v_x_6980_, 1);
                crate::leanh::lean_inc_n(v_k_6981_, 2);
                v_v_6982_ = crate::leanh::lean_ctor_get(v_x_6980_, 2);
                crate::leanh::lean_inc(v_v_6982_);
                v_l_6983_ = crate::leanh::lean_ctor_get(v_x_6980_, 3);
                crate::leanh::lean_inc(v_l_6983_);
                v_r_6984_ = crate::leanh::lean_ctor_get(v_x_6980_, 4);
                crate::leanh::lean_inc(v_r_6984_);
                crate::leanh::lean_dec(v_x_6980_);
                crate::leanh::lean_inc_ref(v_inst_6978_);
                crate::leanh::lean_inc(v_k_6979_);
                v___x_6985_ = crate::leanh::lean_apply_2(v_inst_6978_, v_k_6979_, v_k_6981_);
                v___x_6986_ = 0;
                v___x_6987_ = (crate::leanh::lean_unbox(v___x_6985_) as u8);
                v___x_6988_ = l_instDecidableEqOrdering(v___x_6987_, v___x_6986_);
                if v___x_6988_ == 0 {
                    crate::leanh::lean_dec(v_l_6983_);
                    crate::leanh::lean_dec(v_v_6982_);
                    crate::leanh::lean_dec(v_k_6981_);
                    v_x_6980_ = v_r_6984_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_6984_);
                    v___x_6990_ = crate::leanh::lean_box(0);
                    v___x_6991_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(
                        v_inst_6978_,
                        v_k_6979_,
                        v___x_6990_,
                        v_l_6983_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6991_) == 0 {
                        v___x_6992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6992_, 0, v_k_6981_);
                        crate::leanh::lean_ctor_set(v___x_6992_, 1, v_v_6982_);
                        return v___x_6992_;
                    } else {
                        crate::leanh::lean_dec(v_v_6982_);
                        crate::leanh::lean_dec(v_k_6981_);
                        v_val_6993_ = crate::leanh::lean_ctor_get(v___x_6991_, 0);
                        crate::leanh::lean_inc(v_val_6993_);
                        crate::leanh::lean_dec_ref_known(v___x_6991_, 1);
                        return v_val_6993_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryGT(
    mut v_00_u03b1_6994_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6995_: *mut crate::leanh::LeanObject,
    mut v_inst_6996_: *mut crate::leanh::LeanObject,
    mut v_inst_6997_: *mut crate::leanh::LeanObject,
    mut v_k_6998_: *mut crate::leanh::LeanObject,
    mut v_x_6999_: *mut crate::leanh::LeanObject,
    mut v_x_7000_: *mut crate::leanh::LeanObject,
    mut v_x_7001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7002_ =
        l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_6996_, v_k_6998_, v_x_6999_);
    return v___x_7002_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(
    mut v_inst_7003_: *mut crate::leanh::LeanObject,
    mut v_k_7004_: *mut crate::leanh::LeanObject,
    mut v_x_7005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7006_ = crate::leanh::lean_ctor_get(v_x_7005_, 1);
                crate::leanh::lean_inc_n(v_k_7006_, 2);
                v_v_7007_ = crate::leanh::lean_ctor_get(v_x_7005_, 2);
                crate::leanh::lean_inc(v_v_7007_);
                v_l_7008_ = crate::leanh::lean_ctor_get(v_x_7005_, 3);
                crate::leanh::lean_inc(v_l_7008_);
                v_r_7009_ = crate::leanh::lean_ctor_get(v_x_7005_, 4);
                crate::leanh::lean_inc(v_r_7009_);
                crate::leanh::lean_dec(v_x_7005_);
                crate::leanh::lean_inc_ref(v_inst_7003_);
                crate::leanh::lean_inc(v_k_7004_);
                v___x_7010_ = crate::leanh::lean_apply_2(v_inst_7003_, v_k_7004_, v_k_7006_);
                v___x_7011_ = (crate::leanh::lean_unbox(v___x_7010_) as u8);
                match v___x_7011_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_7009_);
                        crate::leanh::lean_dec(v_v_7007_);
                        crate::leanh::lean_dec(v_k_7006_);
                        v_x_7005_ = v_l_7008_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_7009_);
                        crate::leanh::lean_dec(v_l_7008_);
                        crate::leanh::lean_dec(v_k_7004_);
                        crate::leanh::lean_dec_ref(v_inst_7003_);
                        v___x_7013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7013_, 0, v_k_7006_);
                        crate::leanh::lean_ctor_set(v___x_7013_, 1, v_v_7007_);
                        return v___x_7013_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_7008_);
                        v___x_7014_ = crate::leanh::lean_box(0);
                        v___x_7015_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(
                            v_inst_7003_,
                            v_k_7004_,
                            v___x_7014_,
                            v_r_7009_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7015_) == 0 {
                            v___x_7016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7016_, 0, v_k_7006_);
                            crate::leanh::lean_ctor_set(v___x_7016_, 1, v_v_7007_);
                            return v___x_7016_;
                        } else {
                            crate::leanh::lean_dec(v_v_7007_);
                            crate::leanh::lean_dec(v_k_7006_);
                            v_val_7017_ = crate::leanh::lean_ctor_get(v___x_7015_, 0);
                            crate::leanh::lean_inc(v_val_7017_);
                            crate::leanh::lean_dec_ref_known(v___x_7015_, 1);
                            return v_val_7017_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLE(
    mut v_00_u03b1_7018_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7019_: *mut crate::leanh::LeanObject,
    mut v_inst_7020_: *mut crate::leanh::LeanObject,
    mut v_inst_7021_: *mut crate::leanh::LeanObject,
    mut v_k_7022_: *mut crate::leanh::LeanObject,
    mut v_x_7023_: *mut crate::leanh::LeanObject,
    mut v_x_7024_: *mut crate::leanh::LeanObject,
    mut v_x_7025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7026_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_7020_, v_k_7022_, v_x_7023_);
    return v___x_7026_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(
    mut v_inst_7027_: *mut crate::leanh::LeanObject,
    mut v_k_7028_: *mut crate::leanh::LeanObject,
    mut v_x_7029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: u8 = 0;
    let mut v___x_7036_: u8 = 0;
    let mut v___x_7037_: u8 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7030_ = crate::leanh::lean_ctor_get(v_x_7029_, 1);
                crate::leanh::lean_inc_n(v_k_7030_, 2);
                v_v_7031_ = crate::leanh::lean_ctor_get(v_x_7029_, 2);
                crate::leanh::lean_inc(v_v_7031_);
                v_l_7032_ = crate::leanh::lean_ctor_get(v_x_7029_, 3);
                crate::leanh::lean_inc(v_l_7032_);
                v_r_7033_ = crate::leanh::lean_ctor_get(v_x_7029_, 4);
                crate::leanh::lean_inc(v_r_7033_);
                crate::leanh::lean_dec(v_x_7029_);
                crate::leanh::lean_inc_ref(v_inst_7027_);
                crate::leanh::lean_inc(v_k_7028_);
                v___x_7034_ = crate::leanh::lean_apply_2(v_inst_7027_, v_k_7028_, v_k_7030_);
                v___x_7035_ = 2;
                v___x_7036_ = (crate::leanh::lean_unbox(v___x_7034_) as u8);
                v___x_7037_ = l_instDecidableEqOrdering(v___x_7036_, v___x_7035_);
                if v___x_7037_ == 0 {
                    crate::leanh::lean_dec(v_r_7033_);
                    crate::leanh::lean_dec(v_v_7031_);
                    crate::leanh::lean_dec(v_k_7030_);
                    v_x_7029_ = v_l_7032_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_7032_);
                    v___x_7039_ = crate::leanh::lean_box(0);
                    v___x_7040_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(
                        v_inst_7027_,
                        v_k_7028_,
                        v___x_7039_,
                        v_r_7033_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7040_) == 0 {
                        v___x_7041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7041_, 0, v_k_7030_);
                        crate::leanh::lean_ctor_set(v___x_7041_, 1, v_v_7031_);
                        return v___x_7041_;
                    } else {
                        crate::leanh::lean_dec(v_v_7031_);
                        crate::leanh::lean_dec(v_k_7030_);
                        v_val_7042_ = crate::leanh::lean_ctor_get(v___x_7040_, 0);
                        crate::leanh::lean_inc(v_val_7042_);
                        crate::leanh::lean_dec_ref_known(v___x_7040_, 1);
                        return v_val_7042_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getEntryLT(
    mut v_00_u03b1_7043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7044_: *mut crate::leanh::LeanObject,
    mut v_inst_7045_: *mut crate::leanh::LeanObject,
    mut v_inst_7046_: *mut crate::leanh::LeanObject,
    mut v_k_7047_: *mut crate::leanh::LeanObject,
    mut v_x_7048_: *mut crate::leanh::LeanObject,
    mut v_x_7049_: *mut crate::leanh::LeanObject,
    mut v_x_7050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7051_ =
        l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_7045_, v_k_7047_, v_x_7048_);
    return v___x_7051_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
    mut v_inst_7052_: *mut crate::leanh::LeanObject,
    mut v_k_7053_: *mut crate::leanh::LeanObject,
    mut v_best_7054_: *mut crate::leanh::LeanObject,
    mut v_a_7055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7055_) == 0 {
                    v_k_7056_ = crate::leanh::lean_ctor_get(v_a_7055_, 1);
                    crate::leanh::lean_inc_n(v_k_7056_, 2);
                    v_l_7057_ = crate::leanh::lean_ctor_get(v_a_7055_, 3);
                    crate::leanh::lean_inc(v_l_7057_);
                    v_r_7058_ = crate::leanh::lean_ctor_get(v_a_7055_, 4);
                    crate::leanh::lean_inc(v_r_7058_);
                    crate::leanh::lean_dec_ref_known(v_a_7055_, 5);
                    crate::leanh::lean_inc_ref(v_inst_7052_);
                    crate::leanh::lean_inc(v_k_7053_);
                    v___x_7059_ = crate::leanh::lean_apply_2(v_inst_7052_, v_k_7053_, v_k_7056_);
                    v___x_7060_ = (crate::leanh::lean_unbox(v___x_7059_) as u8);
                    match v___x_7060_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_7058_);
                            crate::leanh::lean_dec(v_best_7054_);
                            v___x_7061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7061_, 0, v_k_7056_);
                            v_best_7054_ = v___x_7061_;
                            v_a_7055_ = v_l_7057_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_7058_);
                            crate::leanh::lean_dec(v_l_7057_);
                            crate::leanh::lean_dec(v_best_7054_);
                            crate::leanh::lean_dec(v_k_7053_);
                            crate::leanh::lean_dec_ref(v_inst_7052_);
                            v___x_7063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7063_, 0, v_k_7056_);
                            return v___x_7063_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_7057_);
                            crate::leanh::lean_dec(v_k_7056_);
                            v_a_7055_ = v_r_7058_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_7053_);
                    crate::leanh::lean_dec_ref(v_inst_7052_);
                    return v_best_7054_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(
    mut v_00_u03b1_7065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7066_: *mut crate::leanh::LeanObject,
    mut v_inst_7067_: *mut crate::leanh::LeanObject,
    mut v_k_7068_: *mut crate::leanh::LeanObject,
    mut v_best_7069_: *mut crate::leanh::LeanObject,
    mut v_a_7070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7067_,
        v_k_7068_,
        v_best_7069_,
        v_a_7070_,
    );
    return v___x_7071_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(
    mut v_inst_7072_: *mut crate::leanh::LeanObject,
    mut v_k_7073_: *mut crate::leanh::LeanObject,
    mut v_a_7074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7075_ = crate::leanh::lean_box(0);
    v___x_7076_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7072_,
        v_k_7073_,
        v___x_7075_,
        v_a_7074_,
    );
    return v___x_7076_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(
    mut v_00_u03b1_7077_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7078_: *mut crate::leanh::LeanObject,
    mut v_inst_7079_: *mut crate::leanh::LeanObject,
    mut v_k_7080_: *mut crate::leanh::LeanObject,
    mut v_a_7081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7082_ = crate::leanh::lean_box(0);
    v___x_7083_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7079_,
        v_k_7080_,
        v___x_7082_,
        v_a_7081_,
    );
    return v___x_7083_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
    mut v_inst_7084_: *mut crate::leanh::LeanObject,
    mut v_k_7085_: *mut crate::leanh::LeanObject,
    mut v_best_7086_: *mut crate::leanh::LeanObject,
    mut v_a_7087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: u8 = 0;
    let mut v___x_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7087_) == 0 {
                    v_k_7088_ = crate::leanh::lean_ctor_get(v_a_7087_, 1);
                    crate::leanh::lean_inc_n(v_k_7088_, 2);
                    v_l_7089_ = crate::leanh::lean_ctor_get(v_a_7087_, 3);
                    crate::leanh::lean_inc(v_l_7089_);
                    v_r_7090_ = crate::leanh::lean_ctor_get(v_a_7087_, 4);
                    crate::leanh::lean_inc(v_r_7090_);
                    crate::leanh::lean_dec_ref_known(v_a_7087_, 5);
                    crate::leanh::lean_inc_ref(v_inst_7084_);
                    crate::leanh::lean_inc(v_k_7085_);
                    v___x_7091_ = crate::leanh::lean_apply_2(v_inst_7084_, v_k_7085_, v_k_7088_);
                    v___x_7092_ = (crate::leanh::lean_unbox(v___x_7091_) as u8);
                    if v___x_7092_ == 0 {
                        crate::leanh::lean_dec(v_r_7090_);
                        crate::leanh::lean_dec(v_best_7086_);
                        v___x_7093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7093_, 0, v_k_7088_);
                        v_best_7086_ = v___x_7093_;
                        v_a_7087_ = v_l_7089_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_7089_);
                        crate::leanh::lean_dec(v_k_7088_);
                        v_a_7087_ = v_r_7090_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_7085_);
                    crate::leanh::lean_dec_ref(v_inst_7084_);
                    return v_best_7086_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(
    mut v_00_u03b1_7096_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7097_: *mut crate::leanh::LeanObject,
    mut v_inst_7098_: *mut crate::leanh::LeanObject,
    mut v_k_7099_: *mut crate::leanh::LeanObject,
    mut v_best_7100_: *mut crate::leanh::LeanObject,
    mut v_a_7101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7098_,
        v_k_7099_,
        v_best_7100_,
        v_a_7101_,
    );
    return v___x_7102_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(
    mut v_inst_7103_: *mut crate::leanh::LeanObject,
    mut v_k_7104_: *mut crate::leanh::LeanObject,
    mut v_a_7105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7106_ = crate::leanh::lean_box(0);
    v___x_7107_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7103_,
        v_k_7104_,
        v___x_7106_,
        v_a_7105_,
    );
    return v___x_7107_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(
    mut v_00_u03b1_7108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7109_: *mut crate::leanh::LeanObject,
    mut v_inst_7110_: *mut crate::leanh::LeanObject,
    mut v_k_7111_: *mut crate::leanh::LeanObject,
    mut v_a_7112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7113_ = crate::leanh::lean_box(0);
    v___x_7114_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7110_,
        v_k_7111_,
        v___x_7113_,
        v_a_7112_,
    );
    return v___x_7114_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
    mut v_inst_7115_: *mut crate::leanh::LeanObject,
    mut v_k_7116_: *mut crate::leanh::LeanObject,
    mut v_best_7117_: *mut crate::leanh::LeanObject,
    mut v_a_7118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: u8 = 0;
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7118_) == 0 {
                    v_k_7119_ = crate::leanh::lean_ctor_get(v_a_7118_, 1);
                    crate::leanh::lean_inc_n(v_k_7119_, 2);
                    v_l_7120_ = crate::leanh::lean_ctor_get(v_a_7118_, 3);
                    crate::leanh::lean_inc(v_l_7120_);
                    v_r_7121_ = crate::leanh::lean_ctor_get(v_a_7118_, 4);
                    crate::leanh::lean_inc(v_r_7121_);
                    crate::leanh::lean_dec_ref_known(v_a_7118_, 5);
                    crate::leanh::lean_inc_ref(v_inst_7115_);
                    crate::leanh::lean_inc(v_k_7116_);
                    v___x_7122_ = crate::leanh::lean_apply_2(v_inst_7115_, v_k_7116_, v_k_7119_);
                    v___x_7123_ = (crate::leanh::lean_unbox(v___x_7122_) as u8);
                    match v___x_7123_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_7121_);
                            crate::leanh::lean_dec(v_k_7119_);
                            v_a_7118_ = v_l_7120_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_7121_);
                            crate::leanh::lean_dec(v_l_7120_);
                            crate::leanh::lean_dec(v_best_7117_);
                            crate::leanh::lean_dec(v_k_7116_);
                            crate::leanh::lean_dec_ref(v_inst_7115_);
                            v___x_7125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7125_, 0, v_k_7119_);
                            return v___x_7125_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_7120_);
                            crate::leanh::lean_dec(v_best_7117_);
                            v___x_7126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7126_, 0, v_k_7119_);
                            v_best_7117_ = v___x_7126_;
                            v_a_7118_ = v_r_7121_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_7116_);
                    crate::leanh::lean_dec_ref(v_inst_7115_);
                    return v_best_7117_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(
    mut v_00_u03b1_7128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7129_: *mut crate::leanh::LeanObject,
    mut v_inst_7130_: *mut crate::leanh::LeanObject,
    mut v_k_7131_: *mut crate::leanh::LeanObject,
    mut v_best_7132_: *mut crate::leanh::LeanObject,
    mut v_a_7133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7134_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7130_,
        v_k_7131_,
        v_best_7132_,
        v_a_7133_,
    );
    return v___x_7134_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(
    mut v_inst_7135_: *mut crate::leanh::LeanObject,
    mut v_k_7136_: *mut crate::leanh::LeanObject,
    mut v_a_7137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7138_ = crate::leanh::lean_box(0);
    v___x_7139_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7135_,
        v_k_7136_,
        v___x_7138_,
        v_a_7137_,
    );
    return v___x_7139_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(
    mut v_00_u03b1_7140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7141_: *mut crate::leanh::LeanObject,
    mut v_inst_7142_: *mut crate::leanh::LeanObject,
    mut v_k_7143_: *mut crate::leanh::LeanObject,
    mut v_a_7144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7145_ = crate::leanh::lean_box(0);
    v___x_7146_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7142_,
        v_k_7143_,
        v___x_7145_,
        v_a_7144_,
    );
    return v___x_7146_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
    mut v_inst_7147_: *mut crate::leanh::LeanObject,
    mut v_k_7148_: *mut crate::leanh::LeanObject,
    mut v_best_7149_: *mut crate::leanh::LeanObject,
    mut v_a_7150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: u8 = 0;
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7150_) == 0 {
                    v_k_7151_ = crate::leanh::lean_ctor_get(v_a_7150_, 1);
                    crate::leanh::lean_inc_n(v_k_7151_, 2);
                    v_l_7152_ = crate::leanh::lean_ctor_get(v_a_7150_, 3);
                    crate::leanh::lean_inc(v_l_7152_);
                    v_r_7153_ = crate::leanh::lean_ctor_get(v_a_7150_, 4);
                    crate::leanh::lean_inc(v_r_7153_);
                    crate::leanh::lean_dec_ref_known(v_a_7150_, 5);
                    crate::leanh::lean_inc_ref(v_inst_7147_);
                    crate::leanh::lean_inc(v_k_7148_);
                    v___x_7154_ = crate::leanh::lean_apply_2(v_inst_7147_, v_k_7148_, v_k_7151_);
                    v___x_7155_ = (crate::leanh::lean_unbox(v___x_7154_) as u8);
                    if v___x_7155_ == 2 {
                        crate::leanh::lean_dec(v_l_7152_);
                        crate::leanh::lean_dec(v_best_7149_);
                        v___x_7156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7156_, 0, v_k_7151_);
                        v_best_7149_ = v___x_7156_;
                        v_a_7150_ = v_r_7153_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_7153_);
                        crate::leanh::lean_dec(v_k_7151_);
                        v_a_7150_ = v_l_7152_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_7148_);
                    crate::leanh::lean_dec_ref(v_inst_7147_);
                    return v_best_7149_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(
    mut v_00_u03b1_7159_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7160_: *mut crate::leanh::LeanObject,
    mut v_inst_7161_: *mut crate::leanh::LeanObject,
    mut v_k_7162_: *mut crate::leanh::LeanObject,
    mut v_best_7163_: *mut crate::leanh::LeanObject,
    mut v_a_7164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7165_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7161_,
        v_k_7162_,
        v_best_7163_,
        v_a_7164_,
    );
    return v___x_7165_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(
    mut v_inst_7166_: *mut crate::leanh::LeanObject,
    mut v_k_7167_: *mut crate::leanh::LeanObject,
    mut v_a_7168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7169_ = crate::leanh::lean_box(0);
    v___x_7170_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7166_,
        v_k_7167_,
        v___x_7169_,
        v_a_7168_,
    );
    return v___x_7170_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(
    mut v_00_u03b1_7171_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7172_: *mut crate::leanh::LeanObject,
    mut v_inst_7173_: *mut crate::leanh::LeanObject,
    mut v_k_7174_: *mut crate::leanh::LeanObject,
    mut v_a_7175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7176_ = crate::leanh::lean_box(0);
    v___x_7177_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7173_,
        v_k_7174_,
        v___x_7176_,
        v_a_7175_,
    );
    return v___x_7177_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(
    mut v_inst_7178_: *mut crate::leanh::LeanObject,
    mut v_inst_7179_: *mut crate::leanh::LeanObject,
    mut v_k_7180_: *mut crate::leanh::LeanObject,
    mut v_t_7181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7182_ = crate::leanh::lean_box(0);
    v___x_7183_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7178_,
        v_k_7180_,
        v___x_7182_,
        v_t_7181_,
    );
    if crate::leanh::lean_obj_tag(v___x_7183_) == 0 {
        let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7184_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7185_ = l_panic___redArg(v_inst_7179_, v___x_7184_);
        return v___x_7185_;
    } else {
        let mut v_val_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7186_ = crate::leanh::lean_ctor_get(v___x_7183_, 0);
        crate::leanh::lean_inc(v_val_7186_);
        crate::leanh::lean_dec_ref_known(v___x_7183_, 1);
        return v_val_7186_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(
    mut v_inst_7187_: *mut crate::leanh::LeanObject,
    mut v_inst_7188_: *mut crate::leanh::LeanObject,
    mut v_k_7189_: *mut crate::leanh::LeanObject,
    mut v_t_7190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7191_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(
        v_inst_7187_,
        v_inst_7188_,
        v_k_7189_,
        v_t_7190_,
    );
    crate::leanh::lean_dec(v_inst_7188_);
    return v_res_7191_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(
    mut v_00_u03b1_7192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7193_: *mut crate::leanh::LeanObject,
    mut v_inst_7194_: *mut crate::leanh::LeanObject,
    mut v_inst_7195_: *mut crate::leanh::LeanObject,
    mut v_k_7196_: *mut crate::leanh::LeanObject,
    mut v_t_7197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7198_ = crate::leanh::lean_box(0);
    v___x_7199_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7194_,
        v_k_7196_,
        v___x_7198_,
        v_t_7197_,
    );
    if crate::leanh::lean_obj_tag(v___x_7199_) == 0 {
        let mut v___x_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7200_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7201_ = l_panic___redArg(v_inst_7195_, v___x_7200_);
        return v___x_7201_;
    } else {
        let mut v_val_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7202_ = crate::leanh::lean_ctor_get(v___x_7199_, 0);
        crate::leanh::lean_inc(v_val_7202_);
        crate::leanh::lean_dec_ref_known(v___x_7199_, 1);
        return v_val_7202_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(
    mut v_00_u03b1_7203_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7204_: *mut crate::leanh::LeanObject,
    mut v_inst_7205_: *mut crate::leanh::LeanObject,
    mut v_inst_7206_: *mut crate::leanh::LeanObject,
    mut v_k_7207_: *mut crate::leanh::LeanObject,
    mut v_t_7208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7209_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(
        v_00_u03b1_7203_,
        v_00_u03b2_7204_,
        v_inst_7205_,
        v_inst_7206_,
        v_k_7207_,
        v_t_7208_,
    );
    crate::leanh::lean_dec(v_inst_7206_);
    return v_res_7209_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(
    mut v_inst_7210_: *mut crate::leanh::LeanObject,
    mut v_inst_7211_: *mut crate::leanh::LeanObject,
    mut v_k_7212_: *mut crate::leanh::LeanObject,
    mut v_t_7213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7214_ = crate::leanh::lean_box(0);
    v___x_7215_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7210_,
        v_k_7212_,
        v___x_7214_,
        v_t_7213_,
    );
    if crate::leanh::lean_obj_tag(v___x_7215_) == 0 {
        let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7216_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7217_ = l_panic___redArg(v_inst_7211_, v___x_7216_);
        return v___x_7217_;
    } else {
        let mut v_val_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7218_ = crate::leanh::lean_ctor_get(v___x_7215_, 0);
        crate::leanh::lean_inc(v_val_7218_);
        crate::leanh::lean_dec_ref_known(v___x_7215_, 1);
        return v_val_7218_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(
    mut v_inst_7219_: *mut crate::leanh::LeanObject,
    mut v_inst_7220_: *mut crate::leanh::LeanObject,
    mut v_k_7221_: *mut crate::leanh::LeanObject,
    mut v_t_7222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7223_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(
        v_inst_7219_,
        v_inst_7220_,
        v_k_7221_,
        v_t_7222_,
    );
    crate::leanh::lean_dec(v_inst_7220_);
    return v_res_7223_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(
    mut v_00_u03b1_7224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7225_: *mut crate::leanh::LeanObject,
    mut v_inst_7226_: *mut crate::leanh::LeanObject,
    mut v_inst_7227_: *mut crate::leanh::LeanObject,
    mut v_k_7228_: *mut crate::leanh::LeanObject,
    mut v_t_7229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7230_ = crate::leanh::lean_box(0);
    v___x_7231_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7226_,
        v_k_7228_,
        v___x_7230_,
        v_t_7229_,
    );
    if crate::leanh::lean_obj_tag(v___x_7231_) == 0 {
        let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7232_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7233_ = l_panic___redArg(v_inst_7227_, v___x_7232_);
        return v___x_7233_;
    } else {
        let mut v_val_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7234_ = crate::leanh::lean_ctor_get(v___x_7231_, 0);
        crate::leanh::lean_inc(v_val_7234_);
        crate::leanh::lean_dec_ref_known(v___x_7231_, 1);
        return v_val_7234_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(
    mut v_00_u03b1_7235_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7236_: *mut crate::leanh::LeanObject,
    mut v_inst_7237_: *mut crate::leanh::LeanObject,
    mut v_inst_7238_: *mut crate::leanh::LeanObject,
    mut v_k_7239_: *mut crate::leanh::LeanObject,
    mut v_t_7240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7241_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(
        v_00_u03b1_7235_,
        v_00_u03b2_7236_,
        v_inst_7237_,
        v_inst_7238_,
        v_k_7239_,
        v_t_7240_,
    );
    crate::leanh::lean_dec(v_inst_7238_);
    return v_res_7241_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(
    mut v_inst_7242_: *mut crate::leanh::LeanObject,
    mut v_inst_7243_: *mut crate::leanh::LeanObject,
    mut v_k_7244_: *mut crate::leanh::LeanObject,
    mut v_t_7245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7246_ = crate::leanh::lean_box(0);
    v___x_7247_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7242_,
        v_k_7244_,
        v___x_7246_,
        v_t_7245_,
    );
    if crate::leanh::lean_obj_tag(v___x_7247_) == 0 {
        let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7248_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7249_ = l_panic___redArg(v_inst_7243_, v___x_7248_);
        return v___x_7249_;
    } else {
        let mut v_val_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7250_ = crate::leanh::lean_ctor_get(v___x_7247_, 0);
        crate::leanh::lean_inc(v_val_7250_);
        crate::leanh::lean_dec_ref_known(v___x_7247_, 1);
        return v_val_7250_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(
    mut v_inst_7251_: *mut crate::leanh::LeanObject,
    mut v_inst_7252_: *mut crate::leanh::LeanObject,
    mut v_k_7253_: *mut crate::leanh::LeanObject,
    mut v_t_7254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7255_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(
        v_inst_7251_,
        v_inst_7252_,
        v_k_7253_,
        v_t_7254_,
    );
    crate::leanh::lean_dec(v_inst_7252_);
    return v_res_7255_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(
    mut v_00_u03b1_7256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7257_: *mut crate::leanh::LeanObject,
    mut v_inst_7258_: *mut crate::leanh::LeanObject,
    mut v_inst_7259_: *mut crate::leanh::LeanObject,
    mut v_k_7260_: *mut crate::leanh::LeanObject,
    mut v_t_7261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7262_ = crate::leanh::lean_box(0);
    v___x_7263_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7258_,
        v_k_7260_,
        v___x_7262_,
        v_t_7261_,
    );
    if crate::leanh::lean_obj_tag(v___x_7263_) == 0 {
        let mut v___x_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7264_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7265_ = l_panic___redArg(v_inst_7259_, v___x_7264_);
        return v___x_7265_;
    } else {
        let mut v_val_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7266_ = crate::leanh::lean_ctor_get(v___x_7263_, 0);
        crate::leanh::lean_inc(v_val_7266_);
        crate::leanh::lean_dec_ref_known(v___x_7263_, 1);
        return v_val_7266_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(
    mut v_00_u03b1_7267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7268_: *mut crate::leanh::LeanObject,
    mut v_inst_7269_: *mut crate::leanh::LeanObject,
    mut v_inst_7270_: *mut crate::leanh::LeanObject,
    mut v_k_7271_: *mut crate::leanh::LeanObject,
    mut v_t_7272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7273_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(
        v_00_u03b1_7267_,
        v_00_u03b2_7268_,
        v_inst_7269_,
        v_inst_7270_,
        v_k_7271_,
        v_t_7272_,
    );
    crate::leanh::lean_dec(v_inst_7270_);
    return v_res_7273_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(
    mut v_inst_7274_: *mut crate::leanh::LeanObject,
    mut v_inst_7275_: *mut crate::leanh::LeanObject,
    mut v_k_7276_: *mut crate::leanh::LeanObject,
    mut v_t_7277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7278_ = crate::leanh::lean_box(0);
    v___x_7279_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7274_,
        v_k_7276_,
        v___x_7278_,
        v_t_7277_,
    );
    if crate::leanh::lean_obj_tag(v___x_7279_) == 0 {
        let mut v___x_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7280_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7281_ = l_panic___redArg(v_inst_7275_, v___x_7280_);
        return v___x_7281_;
    } else {
        let mut v_val_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7282_ = crate::leanh::lean_ctor_get(v___x_7279_, 0);
        crate::leanh::lean_inc(v_val_7282_);
        crate::leanh::lean_dec_ref_known(v___x_7279_, 1);
        return v_val_7282_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(
    mut v_inst_7283_: *mut crate::leanh::LeanObject,
    mut v_inst_7284_: *mut crate::leanh::LeanObject,
    mut v_k_7285_: *mut crate::leanh::LeanObject,
    mut v_t_7286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7287_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(
        v_inst_7283_,
        v_inst_7284_,
        v_k_7285_,
        v_t_7286_,
    );
    crate::leanh::lean_dec(v_inst_7284_);
    return v_res_7287_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(
    mut v_00_u03b1_7288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7289_: *mut crate::leanh::LeanObject,
    mut v_inst_7290_: *mut crate::leanh::LeanObject,
    mut v_inst_7291_: *mut crate::leanh::LeanObject,
    mut v_k_7292_: *mut crate::leanh::LeanObject,
    mut v_t_7293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7294_ = crate::leanh::lean_box(0);
    v___x_7295_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7290_,
        v_k_7292_,
        v___x_7294_,
        v_t_7293_,
    );
    if crate::leanh::lean_obj_tag(v___x_7295_) == 0 {
        let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7296_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_7297_ = l_panic___redArg(v_inst_7291_, v___x_7296_);
        return v___x_7297_;
    } else {
        let mut v_val_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7298_ = crate::leanh::lean_ctor_get(v___x_7295_, 0);
        crate::leanh::lean_inc(v_val_7298_);
        crate::leanh::lean_dec_ref_known(v___x_7295_, 1);
        return v_val_7298_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(
    mut v_00_u03b1_7299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7300_: *mut crate::leanh::LeanObject,
    mut v_inst_7301_: *mut crate::leanh::LeanObject,
    mut v_inst_7302_: *mut crate::leanh::LeanObject,
    mut v_k_7303_: *mut crate::leanh::LeanObject,
    mut v_t_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7305_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(
        v_00_u03b1_7299_,
        v_00_u03b2_7300_,
        v_inst_7301_,
        v_inst_7302_,
        v_k_7303_,
        v_t_7304_,
    );
    crate::leanh::lean_dec(v_inst_7302_);
    return v_res_7305_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(
    mut v_inst_7306_: *mut crate::leanh::LeanObject,
    mut v_k_7307_: *mut crate::leanh::LeanObject,
    mut v_t_7308_: *mut crate::leanh::LeanObject,
    mut v_fallback_7309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7310_ = crate::leanh::lean_box(0);
    v___x_7311_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7306_,
        v_k_7307_,
        v___x_7310_,
        v_t_7308_,
    );
    if crate::leanh::lean_obj_tag(v___x_7311_) == 0 {
        crate::leanh::lean_inc(v_fallback_7309_);
        return v_fallback_7309_;
    } else {
        let mut v_val_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7312_ = crate::leanh::lean_ctor_get(v___x_7311_, 0);
        crate::leanh::lean_inc(v_val_7312_);
        crate::leanh::lean_dec_ref_known(v___x_7311_, 1);
        return v_val_7312_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(
    mut v_inst_7313_: *mut crate::leanh::LeanObject,
    mut v_k_7314_: *mut crate::leanh::LeanObject,
    mut v_t_7315_: *mut crate::leanh::LeanObject,
    mut v_fallback_7316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7317_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(
        v_inst_7313_,
        v_k_7314_,
        v_t_7315_,
        v_fallback_7316_,
    );
    crate::leanh::lean_dec(v_fallback_7316_);
    return v_res_7317_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGED(
    mut v_00_u03b1_7318_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7319_: *mut crate::leanh::LeanObject,
    mut v_inst_7320_: *mut crate::leanh::LeanObject,
    mut v_k_7321_: *mut crate::leanh::LeanObject,
    mut v_t_7322_: *mut crate::leanh::LeanObject,
    mut v_fallback_7323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7324_ = crate::leanh::lean_box(0);
    v___x_7325_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
        v_inst_7320_,
        v_k_7321_,
        v___x_7324_,
        v_t_7322_,
    );
    if crate::leanh::lean_obj_tag(v___x_7325_) == 0 {
        crate::leanh::lean_inc(v_fallback_7323_);
        return v_fallback_7323_;
    } else {
        let mut v_val_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7326_ = crate::leanh::lean_ctor_get(v___x_7325_, 0);
        crate::leanh::lean_inc(v_val_7326_);
        crate::leanh::lean_dec_ref_known(v___x_7325_, 1);
        return v_val_7326_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(
    mut v_00_u03b1_7327_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7328_: *mut crate::leanh::LeanObject,
    mut v_inst_7329_: *mut crate::leanh::LeanObject,
    mut v_k_7330_: *mut crate::leanh::LeanObject,
    mut v_t_7331_: *mut crate::leanh::LeanObject,
    mut v_fallback_7332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7333_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(
        v_00_u03b1_7327_,
        v_00_u03b2_7328_,
        v_inst_7329_,
        v_k_7330_,
        v_t_7331_,
        v_fallback_7332_,
    );
    crate::leanh::lean_dec(v_fallback_7332_);
    return v_res_7333_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(
    mut v_inst_7334_: *mut crate::leanh::LeanObject,
    mut v_k_7335_: *mut crate::leanh::LeanObject,
    mut v_t_7336_: *mut crate::leanh::LeanObject,
    mut v_fallback_7337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7338_ = crate::leanh::lean_box(0);
    v___x_7339_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7334_,
        v_k_7335_,
        v___x_7338_,
        v_t_7336_,
    );
    if crate::leanh::lean_obj_tag(v___x_7339_) == 0 {
        crate::leanh::lean_inc(v_fallback_7337_);
        return v_fallback_7337_;
    } else {
        let mut v_val_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7340_ = crate::leanh::lean_ctor_get(v___x_7339_, 0);
        crate::leanh::lean_inc(v_val_7340_);
        crate::leanh::lean_dec_ref_known(v___x_7339_, 1);
        return v_val_7340_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(
    mut v_inst_7341_: *mut crate::leanh::LeanObject,
    mut v_k_7342_: *mut crate::leanh::LeanObject,
    mut v_t_7343_: *mut crate::leanh::LeanObject,
    mut v_fallback_7344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7345_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(
        v_inst_7341_,
        v_k_7342_,
        v_t_7343_,
        v_fallback_7344_,
    );
    crate::leanh::lean_dec(v_fallback_7344_);
    return v_res_7345_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGTD(
    mut v_00_u03b1_7346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7347_: *mut crate::leanh::LeanObject,
    mut v_inst_7348_: *mut crate::leanh::LeanObject,
    mut v_k_7349_: *mut crate::leanh::LeanObject,
    mut v_t_7350_: *mut crate::leanh::LeanObject,
    mut v_fallback_7351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7352_ = crate::leanh::lean_box(0);
    v___x_7353_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
        v_inst_7348_,
        v_k_7349_,
        v___x_7352_,
        v_t_7350_,
    );
    if crate::leanh::lean_obj_tag(v___x_7353_) == 0 {
        crate::leanh::lean_inc(v_fallback_7351_);
        return v_fallback_7351_;
    } else {
        let mut v_val_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7354_ = crate::leanh::lean_ctor_get(v___x_7353_, 0);
        crate::leanh::lean_inc(v_val_7354_);
        crate::leanh::lean_dec_ref_known(v___x_7353_, 1);
        return v_val_7354_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(
    mut v_00_u03b1_7355_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7356_: *mut crate::leanh::LeanObject,
    mut v_inst_7357_: *mut crate::leanh::LeanObject,
    mut v_k_7358_: *mut crate::leanh::LeanObject,
    mut v_t_7359_: *mut crate::leanh::LeanObject,
    mut v_fallback_7360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7361_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(
        v_00_u03b1_7355_,
        v_00_u03b2_7356_,
        v_inst_7357_,
        v_k_7358_,
        v_t_7359_,
        v_fallback_7360_,
    );
    crate::leanh::lean_dec(v_fallback_7360_);
    return v_res_7361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(
    mut v_inst_7362_: *mut crate::leanh::LeanObject,
    mut v_k_7363_: *mut crate::leanh::LeanObject,
    mut v_t_7364_: *mut crate::leanh::LeanObject,
    mut v_fallback_7365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7366_ = crate::leanh::lean_box(0);
    v___x_7367_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7362_,
        v_k_7363_,
        v___x_7366_,
        v_t_7364_,
    );
    if crate::leanh::lean_obj_tag(v___x_7367_) == 0 {
        crate::leanh::lean_inc(v_fallback_7365_);
        return v_fallback_7365_;
    } else {
        let mut v_val_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7368_ = crate::leanh::lean_ctor_get(v___x_7367_, 0);
        crate::leanh::lean_inc(v_val_7368_);
        crate::leanh::lean_dec_ref_known(v___x_7367_, 1);
        return v_val_7368_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(
    mut v_inst_7369_: *mut crate::leanh::LeanObject,
    mut v_k_7370_: *mut crate::leanh::LeanObject,
    mut v_t_7371_: *mut crate::leanh::LeanObject,
    mut v_fallback_7372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7373_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(
        v_inst_7369_,
        v_k_7370_,
        v_t_7371_,
        v_fallback_7372_,
    );
    crate::leanh::lean_dec(v_fallback_7372_);
    return v_res_7373_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLED(
    mut v_00_u03b1_7374_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7375_: *mut crate::leanh::LeanObject,
    mut v_inst_7376_: *mut crate::leanh::LeanObject,
    mut v_k_7377_: *mut crate::leanh::LeanObject,
    mut v_t_7378_: *mut crate::leanh::LeanObject,
    mut v_fallback_7379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7380_ = crate::leanh::lean_box(0);
    v___x_7381_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
        v_inst_7376_,
        v_k_7377_,
        v___x_7380_,
        v_t_7378_,
    );
    if crate::leanh::lean_obj_tag(v___x_7381_) == 0 {
        crate::leanh::lean_inc(v_fallback_7379_);
        return v_fallback_7379_;
    } else {
        let mut v_val_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7382_ = crate::leanh::lean_ctor_get(v___x_7381_, 0);
        crate::leanh::lean_inc(v_val_7382_);
        crate::leanh::lean_dec_ref_known(v___x_7381_, 1);
        return v_val_7382_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(
    mut v_00_u03b1_7383_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7384_: *mut crate::leanh::LeanObject,
    mut v_inst_7385_: *mut crate::leanh::LeanObject,
    mut v_k_7386_: *mut crate::leanh::LeanObject,
    mut v_t_7387_: *mut crate::leanh::LeanObject,
    mut v_fallback_7388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7389_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(
        v_00_u03b1_7383_,
        v_00_u03b2_7384_,
        v_inst_7385_,
        v_k_7386_,
        v_t_7387_,
        v_fallback_7388_,
    );
    crate::leanh::lean_dec(v_fallback_7388_);
    return v_res_7389_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(
    mut v_inst_7390_: *mut crate::leanh::LeanObject,
    mut v_k_7391_: *mut crate::leanh::LeanObject,
    mut v_t_7392_: *mut crate::leanh::LeanObject,
    mut v_fallback_7393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7394_ = crate::leanh::lean_box(0);
    v___x_7395_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7390_,
        v_k_7391_,
        v___x_7394_,
        v_t_7392_,
    );
    if crate::leanh::lean_obj_tag(v___x_7395_) == 0 {
        crate::leanh::lean_inc(v_fallback_7393_);
        return v_fallback_7393_;
    } else {
        let mut v_val_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7396_ = crate::leanh::lean_ctor_get(v___x_7395_, 0);
        crate::leanh::lean_inc(v_val_7396_);
        crate::leanh::lean_dec_ref_known(v___x_7395_, 1);
        return v_val_7396_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(
    mut v_inst_7397_: *mut crate::leanh::LeanObject,
    mut v_k_7398_: *mut crate::leanh::LeanObject,
    mut v_t_7399_: *mut crate::leanh::LeanObject,
    mut v_fallback_7400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7401_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(
        v_inst_7397_,
        v_k_7398_,
        v_t_7399_,
        v_fallback_7400_,
    );
    crate::leanh::lean_dec(v_fallback_7400_);
    return v_res_7401_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLTD(
    mut v_00_u03b1_7402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7403_: *mut crate::leanh::LeanObject,
    mut v_inst_7404_: *mut crate::leanh::LeanObject,
    mut v_k_7405_: *mut crate::leanh::LeanObject,
    mut v_t_7406_: *mut crate::leanh::LeanObject,
    mut v_fallback_7407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7408_ = crate::leanh::lean_box(0);
    v___x_7409_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
        v_inst_7404_,
        v_k_7405_,
        v___x_7408_,
        v_t_7406_,
    );
    if crate::leanh::lean_obj_tag(v___x_7409_) == 0 {
        crate::leanh::lean_inc(v_fallback_7407_);
        return v_fallback_7407_;
    } else {
        let mut v_val_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7410_ = crate::leanh::lean_ctor_get(v___x_7409_, 0);
        crate::leanh::lean_inc(v_val_7410_);
        crate::leanh::lean_dec_ref_known(v___x_7409_, 1);
        return v_val_7410_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(
    mut v_00_u03b1_7411_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7412_: *mut crate::leanh::LeanObject,
    mut v_inst_7413_: *mut crate::leanh::LeanObject,
    mut v_k_7414_: *mut crate::leanh::LeanObject,
    mut v_t_7415_: *mut crate::leanh::LeanObject,
    mut v_fallback_7416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7417_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(
        v_00_u03b1_7411_,
        v_00_u03b2_7412_,
        v_inst_7413_,
        v_k_7414_,
        v_t_7415_,
        v_fallback_7416_,
    );
    crate::leanh::lean_dec(v_fallback_7416_);
    return v_res_7417_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(
    mut v_inst_7418_: *mut crate::leanh::LeanObject,
    mut v_k_7419_: *mut crate::leanh::LeanObject,
    mut v_x_7420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: u8 = 0;
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7421_ = crate::leanh::lean_ctor_get(v_x_7420_, 1);
                crate::leanh::lean_inc_n(v_k_7421_, 2);
                v_l_7422_ = crate::leanh::lean_ctor_get(v_x_7420_, 3);
                crate::leanh::lean_inc(v_l_7422_);
                v_r_7423_ = crate::leanh::lean_ctor_get(v_x_7420_, 4);
                crate::leanh::lean_inc(v_r_7423_);
                crate::leanh::lean_dec(v_x_7420_);
                crate::leanh::lean_inc_ref(v_inst_7418_);
                crate::leanh::lean_inc(v_k_7419_);
                v___x_7424_ = crate::leanh::lean_apply_2(v_inst_7418_, v_k_7419_, v_k_7421_);
                v___x_7425_ = (crate::leanh::lean_unbox(v___x_7424_) as u8);
                match v___x_7425_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_7423_);
                        v___x_7426_ = crate::leanh::lean_box(0);
                        v___x_7427_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(
                            v_inst_7418_,
                            v_k_7419_,
                            v___x_7426_,
                            v_l_7422_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7427_) == 0 {
                            return v_k_7421_;
                        } else {
                            crate::leanh::lean_dec(v_k_7421_);
                            v_val_7428_ = crate::leanh::lean_ctor_get(v___x_7427_, 0);
                            crate::leanh::lean_inc(v_val_7428_);
                            crate::leanh::lean_dec_ref_known(v___x_7427_, 1);
                            return v_val_7428_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_7423_);
                        crate::leanh::lean_dec(v_l_7422_);
                        crate::leanh::lean_dec(v_k_7419_);
                        crate::leanh::lean_dec_ref(v_inst_7418_);
                        return v_k_7421_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_7422_);
                        crate::leanh::lean_dec(v_k_7421_);
                        v_x_7420_ = v_r_7423_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGE(
    mut v_00_u03b1_7430_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7431_: *mut crate::leanh::LeanObject,
    mut v_inst_7432_: *mut crate::leanh::LeanObject,
    mut v_inst_7433_: *mut crate::leanh::LeanObject,
    mut v_k_7434_: *mut crate::leanh::LeanObject,
    mut v_x_7435_: *mut crate::leanh::LeanObject,
    mut v_x_7436_: *mut crate::leanh::LeanObject,
    mut v_x_7437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7438_ =
        l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_7432_, v_k_7434_, v_x_7435_);
    return v___x_7438_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(
    mut v_inst_7439_: *mut crate::leanh::LeanObject,
    mut v_k_7440_: *mut crate::leanh::LeanObject,
    mut v_x_7441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: u8 = 0;
    let mut v___x_7447_: u8 = 0;
    let mut v___x_7448_: u8 = 0;
    let mut v___x_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7442_ = crate::leanh::lean_ctor_get(v_x_7441_, 1);
                crate::leanh::lean_inc_n(v_k_7442_, 2);
                v_l_7443_ = crate::leanh::lean_ctor_get(v_x_7441_, 3);
                crate::leanh::lean_inc(v_l_7443_);
                v_r_7444_ = crate::leanh::lean_ctor_get(v_x_7441_, 4);
                crate::leanh::lean_inc(v_r_7444_);
                crate::leanh::lean_dec(v_x_7441_);
                crate::leanh::lean_inc_ref(v_inst_7439_);
                crate::leanh::lean_inc(v_k_7440_);
                v___x_7445_ = crate::leanh::lean_apply_2(v_inst_7439_, v_k_7440_, v_k_7442_);
                v___x_7446_ = 0;
                v___x_7447_ = (crate::leanh::lean_unbox(v___x_7445_) as u8);
                v___x_7448_ = l_instDecidableEqOrdering(v___x_7447_, v___x_7446_);
                if v___x_7448_ == 0 {
                    crate::leanh::lean_dec(v_l_7443_);
                    crate::leanh::lean_dec(v_k_7442_);
                    v_x_7441_ = v_r_7444_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_7444_);
                    v___x_7450_ = crate::leanh::lean_box(0);
                    v___x_7451_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(
                        v_inst_7439_,
                        v_k_7440_,
                        v___x_7450_,
                        v_l_7443_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7451_) == 0 {
                        return v_k_7442_;
                    } else {
                        crate::leanh::lean_dec(v_k_7442_);
                        v_val_7452_ = crate::leanh::lean_ctor_get(v___x_7451_, 0);
                        crate::leanh::lean_inc(v_val_7452_);
                        crate::leanh::lean_dec_ref_known(v___x_7451_, 1);
                        return v_val_7452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyGT(
    mut v_00_u03b1_7453_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7454_: *mut crate::leanh::LeanObject,
    mut v_inst_7455_: *mut crate::leanh::LeanObject,
    mut v_inst_7456_: *mut crate::leanh::LeanObject,
    mut v_k_7457_: *mut crate::leanh::LeanObject,
    mut v_x_7458_: *mut crate::leanh::LeanObject,
    mut v_x_7459_: *mut crate::leanh::LeanObject,
    mut v_x_7460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7461_ =
        l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_7455_, v_k_7457_, v_x_7458_);
    return v___x_7461_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(
    mut v_inst_7462_: *mut crate::leanh::LeanObject,
    mut v_k_7463_: *mut crate::leanh::LeanObject,
    mut v_x_7464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: u8 = 0;
    let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7465_ = crate::leanh::lean_ctor_get(v_x_7464_, 1);
                crate::leanh::lean_inc_n(v_k_7465_, 2);
                v_l_7466_ = crate::leanh::lean_ctor_get(v_x_7464_, 3);
                crate::leanh::lean_inc(v_l_7466_);
                v_r_7467_ = crate::leanh::lean_ctor_get(v_x_7464_, 4);
                crate::leanh::lean_inc(v_r_7467_);
                crate::leanh::lean_dec(v_x_7464_);
                crate::leanh::lean_inc_ref(v_inst_7462_);
                crate::leanh::lean_inc(v_k_7463_);
                v___x_7468_ = crate::leanh::lean_apply_2(v_inst_7462_, v_k_7463_, v_k_7465_);
                v___x_7469_ = (crate::leanh::lean_unbox(v___x_7468_) as u8);
                match v___x_7469_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_7467_);
                        crate::leanh::lean_dec(v_k_7465_);
                        v_x_7464_ = v_l_7466_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_7467_);
                        crate::leanh::lean_dec(v_l_7466_);
                        crate::leanh::lean_dec(v_k_7463_);
                        crate::leanh::lean_dec_ref(v_inst_7462_);
                        return v_k_7465_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_7466_);
                        v___x_7471_ = crate::leanh::lean_box(0);
                        v___x_7472_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(
                            v_inst_7462_,
                            v_k_7463_,
                            v___x_7471_,
                            v_r_7467_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7472_) == 0 {
                            return v_k_7465_;
                        } else {
                            crate::leanh::lean_dec(v_k_7465_);
                            v_val_7473_ = crate::leanh::lean_ctor_get(v___x_7472_, 0);
                            crate::leanh::lean_inc(v_val_7473_);
                            crate::leanh::lean_dec_ref_known(v___x_7472_, 1);
                            return v_val_7473_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLE(
    mut v_00_u03b1_7474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7475_: *mut crate::leanh::LeanObject,
    mut v_inst_7476_: *mut crate::leanh::LeanObject,
    mut v_inst_7477_: *mut crate::leanh::LeanObject,
    mut v_k_7478_: *mut crate::leanh::LeanObject,
    mut v_x_7479_: *mut crate::leanh::LeanObject,
    mut v_x_7480_: *mut crate::leanh::LeanObject,
    mut v_x_7481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7482_ =
        l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_7476_, v_k_7478_, v_x_7479_);
    return v___x_7482_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(
    mut v_inst_7483_: *mut crate::leanh::LeanObject,
    mut v_k_7484_: *mut crate::leanh::LeanObject,
    mut v_x_7485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: u8 = 0;
    let mut v___x_7491_: u8 = 0;
    let mut v___x_7492_: u8 = 0;
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7486_ = crate::leanh::lean_ctor_get(v_x_7485_, 1);
                crate::leanh::lean_inc_n(v_k_7486_, 2);
                v_l_7487_ = crate::leanh::lean_ctor_get(v_x_7485_, 3);
                crate::leanh::lean_inc(v_l_7487_);
                v_r_7488_ = crate::leanh::lean_ctor_get(v_x_7485_, 4);
                crate::leanh::lean_inc(v_r_7488_);
                crate::leanh::lean_dec(v_x_7485_);
                crate::leanh::lean_inc_ref(v_inst_7483_);
                crate::leanh::lean_inc(v_k_7484_);
                v___x_7489_ = crate::leanh::lean_apply_2(v_inst_7483_, v_k_7484_, v_k_7486_);
                v___x_7490_ = 2;
                v___x_7491_ = (crate::leanh::lean_unbox(v___x_7489_) as u8);
                v___x_7492_ = l_instDecidableEqOrdering(v___x_7491_, v___x_7490_);
                if v___x_7492_ == 0 {
                    crate::leanh::lean_dec(v_r_7488_);
                    crate::leanh::lean_dec(v_k_7486_);
                    v_x_7485_ = v_l_7487_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_7487_);
                    v___x_7494_ = crate::leanh::lean_box(0);
                    v___x_7495_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(
                        v_inst_7483_,
                        v_k_7484_,
                        v___x_7494_,
                        v_r_7488_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7495_) == 0 {
                        return v_k_7486_;
                    } else {
                        crate::leanh::lean_dec(v_k_7486_);
                        v_val_7496_ = crate::leanh::lean_ctor_get(v___x_7495_, 0);
                        crate::leanh::lean_inc(v_val_7496_);
                        crate::leanh::lean_dec_ref_known(v___x_7495_, 1);
                        return v_val_7496_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_getKeyLT(
    mut v_00_u03b1_7497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7498_: *mut crate::leanh::LeanObject,
    mut v_inst_7499_: *mut crate::leanh::LeanObject,
    mut v_inst_7500_: *mut crate::leanh::LeanObject,
    mut v_k_7501_: *mut crate::leanh::LeanObject,
    mut v_x_7502_: *mut crate::leanh::LeanObject,
    mut v_x_7503_: *mut crate::leanh::LeanObject,
    mut v_x_7504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7505_ =
        l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_7499_, v_k_7501_, v_x_7502_);
    return v___x_7505_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(
    mut v_x_7506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7506_) == 0 {
                    v_l_7507_ = crate::leanh::lean_ctor_get(v_x_7506_, 3);
                    if crate::leanh::lean_obj_tag(v_l_7507_) == 0 {
                        v_x_7506_ = v_l_7507_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7509_ = crate::leanh::lean_ctor_get(v_x_7506_, 1);
                        v_v_7510_ = crate::leanh::lean_ctor_get(v_x_7506_, 2);
                        crate::leanh::lean_inc(v_v_7510_);
                        crate::leanh::lean_inc(v_k_7509_);
                        v___x_7511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7511_, 0, v_k_7509_);
                        crate::leanh::lean_ctor_set(v___x_7511_, 1, v_v_7510_);
                        v___x_7512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7512_, 0, v___x_7511_);
                        return v___x_7512_;
                    }
                } else {
                    v___x_7513_ = crate::leanh::lean_box(0);
                    return v___x_7513_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(
    mut v_x_7514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7515_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_7514_);
    crate::leanh::lean_dec(v_x_7514_);
    return v_res_7515_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(
    mut v_00_u03b1_7516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7517_: *mut crate::leanh::LeanObject,
    mut v_x_7518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7519_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_7518_);
    return v___x_7519_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(
    mut v_00_u03b1_7520_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7521_: *mut crate::leanh::LeanObject,
    mut v_x_7522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7523_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(
        v_00_u03b1_7520_,
        v_00_u03b2_7521_,
        v_x_7522_,
    );
    crate::leanh::lean_dec(v_x_7522_);
    return v_res_7523_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(
    mut v_x_7524_: *mut crate::leanh::LeanObject,
    mut v_h__1_7525_: *mut crate::leanh::LeanObject,
    mut v_h__2_7526_: *mut crate::leanh::LeanObject,
    mut v_h__3_7527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7524_) == 0 {
        let mut v_l_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7525_);
        v_l_7528_ = crate::leanh::lean_ctor_get(v_x_7524_, 3);
        if crate::leanh::lean_obj_tag(v_l_7528_) == 0 {
            let mut v_size_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_7528_);
            crate::leanh::lean_dec(v_h__2_7526_);
            v_size_7529_ = crate::leanh::lean_ctor_get(v_x_7524_, 0);
            crate::leanh::lean_inc(v_size_7529_);
            v_k_7530_ = crate::leanh::lean_ctor_get(v_x_7524_, 1);
            crate::leanh::lean_inc(v_k_7530_);
            v_v_7531_ = crate::leanh::lean_ctor_get(v_x_7524_, 2);
            crate::leanh::lean_inc(v_v_7531_);
            v_r_7532_ = crate::leanh::lean_ctor_get(v_x_7524_, 4);
            crate::leanh::lean_inc(v_r_7532_);
            crate::leanh::lean_dec_ref_known(v_x_7524_, 5);
            v_size_7533_ = crate::leanh::lean_ctor_get(v_l_7528_, 0);
            crate::leanh::lean_inc(v_size_7533_);
            v_k_7534_ = crate::leanh::lean_ctor_get(v_l_7528_, 1);
            crate::leanh::lean_inc(v_k_7534_);
            v_v_7535_ = crate::leanh::lean_ctor_get(v_l_7528_, 2);
            crate::leanh::lean_inc(v_v_7535_);
            v_l_7536_ = crate::leanh::lean_ctor_get(v_l_7528_, 3);
            crate::leanh::lean_inc(v_l_7536_);
            v_r_7537_ = crate::leanh::lean_ctor_get(v_l_7528_, 4);
            crate::leanh::lean_inc(v_r_7537_);
            crate::leanh::lean_dec_ref_known(v_l_7528_, 5);
            v___x_7538_ = crate::leanh::lean_apply_9(
                v_h__3_7527_,
                v_size_7529_,
                v_k_7530_,
                v_v_7531_,
                v_size_7533_,
                v_k_7534_,
                v_v_7535_,
                v_l_7536_,
                v_r_7537_,
                v_r_7532_,
            );
            return v___x_7538_;
        } else {
            let mut v_size_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7527_);
            v_size_7539_ = crate::leanh::lean_ctor_get(v_x_7524_, 0);
            crate::leanh::lean_inc(v_size_7539_);
            v_k_7540_ = crate::leanh::lean_ctor_get(v_x_7524_, 1);
            crate::leanh::lean_inc(v_k_7540_);
            v_v_7541_ = crate::leanh::lean_ctor_get(v_x_7524_, 2);
            crate::leanh::lean_inc(v_v_7541_);
            v_r_7542_ = crate::leanh::lean_ctor_get(v_x_7524_, 4);
            crate::leanh::lean_inc(v_r_7542_);
            crate::leanh::lean_dec_ref_known(v_x_7524_, 5);
            v___x_7543_ = crate::leanh::lean_apply_4(
                v_h__2_7526_,
                v_size_7539_,
                v_k_7540_,
                v_v_7541_,
                v_r_7542_,
            );
            return v___x_7543_;
        }
    } else {
        let mut v___x_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7527_);
        crate::leanh::lean_dec(v_h__2_7526_);
        v___x_7544_ = crate::leanh::lean_box(0);
        v___x_7545_ = crate::leanh::lean_apply_1(v_h__1_7525_, v___x_7544_);
        return v___x_7545_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(
    mut v_00_u03b1_7546_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7547_: *mut crate::leanh::LeanObject,
    mut v_motive_7548_: *mut crate::leanh::LeanObject,
    mut v_x_7549_: *mut crate::leanh::LeanObject,
    mut v_h__1_7550_: *mut crate::leanh::LeanObject,
    mut v_h__2_7551_: *mut crate::leanh::LeanObject,
    mut v_h__3_7552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7549_) == 0 {
        let mut v_l_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7550_);
        v_l_7553_ = crate::leanh::lean_ctor_get(v_x_7549_, 3);
        if crate::leanh::lean_obj_tag(v_l_7553_) == 0 {
            let mut v_size_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_7553_);
            crate::leanh::lean_dec(v_h__2_7551_);
            v_size_7554_ = crate::leanh::lean_ctor_get(v_x_7549_, 0);
            crate::leanh::lean_inc(v_size_7554_);
            v_k_7555_ = crate::leanh::lean_ctor_get(v_x_7549_, 1);
            crate::leanh::lean_inc(v_k_7555_);
            v_v_7556_ = crate::leanh::lean_ctor_get(v_x_7549_, 2);
            crate::leanh::lean_inc(v_v_7556_);
            v_r_7557_ = crate::leanh::lean_ctor_get(v_x_7549_, 4);
            crate::leanh::lean_inc(v_r_7557_);
            crate::leanh::lean_dec_ref_known(v_x_7549_, 5);
            v_size_7558_ = crate::leanh::lean_ctor_get(v_l_7553_, 0);
            crate::leanh::lean_inc(v_size_7558_);
            v_k_7559_ = crate::leanh::lean_ctor_get(v_l_7553_, 1);
            crate::leanh::lean_inc(v_k_7559_);
            v_v_7560_ = crate::leanh::lean_ctor_get(v_l_7553_, 2);
            crate::leanh::lean_inc(v_v_7560_);
            v_l_7561_ = crate::leanh::lean_ctor_get(v_l_7553_, 3);
            crate::leanh::lean_inc(v_l_7561_);
            v_r_7562_ = crate::leanh::lean_ctor_get(v_l_7553_, 4);
            crate::leanh::lean_inc(v_r_7562_);
            crate::leanh::lean_dec_ref_known(v_l_7553_, 5);
            v___x_7563_ = crate::leanh::lean_apply_9(
                v_h__3_7552_,
                v_size_7554_,
                v_k_7555_,
                v_v_7556_,
                v_size_7558_,
                v_k_7559_,
                v_v_7560_,
                v_l_7561_,
                v_r_7562_,
                v_r_7557_,
            );
            return v___x_7563_;
        } else {
            let mut v_size_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7552_);
            v_size_7564_ = crate::leanh::lean_ctor_get(v_x_7549_, 0);
            crate::leanh::lean_inc(v_size_7564_);
            v_k_7565_ = crate::leanh::lean_ctor_get(v_x_7549_, 1);
            crate::leanh::lean_inc(v_k_7565_);
            v_v_7566_ = crate::leanh::lean_ctor_get(v_x_7549_, 2);
            crate::leanh::lean_inc(v_v_7566_);
            v_r_7567_ = crate::leanh::lean_ctor_get(v_x_7549_, 4);
            crate::leanh::lean_inc(v_r_7567_);
            crate::leanh::lean_dec_ref_known(v_x_7549_, 5);
            v___x_7568_ = crate::leanh::lean_apply_4(
                v_h__2_7551_,
                v_size_7564_,
                v_k_7565_,
                v_v_7566_,
                v_r_7567_,
            );
            return v___x_7568_;
        }
    } else {
        let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7552_);
        crate::leanh::lean_dec(v_h__2_7551_);
        v___x_7569_ = crate::leanh::lean_box(0);
        v___x_7570_ = crate::leanh::lean_apply_1(v_h__1_7550_, v___x_7569_);
        return v___x_7570_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(
    mut v_x_7571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_l_7572_ = crate::leanh::lean_ctor_get(v_x_7571_, 3);
                if crate::leanh::lean_obj_tag(v_l_7572_) == 0 {
                    v_x_7571_ = v_l_7572_;
                    state = 0;
                    continue;
                } else {
                    v_k_7574_ = crate::leanh::lean_ctor_get(v_x_7571_, 1);
                    v_v_7575_ = crate::leanh::lean_ctor_get(v_x_7571_, 2);
                    crate::leanh::lean_inc(v_v_7575_);
                    crate::leanh::lean_inc(v_k_7574_);
                    v___x_7576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7576_, 0, v_k_7574_);
                    crate::leanh::lean_ctor_set(v___x_7576_, 1, v_v_7575_);
                    return v___x_7576_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(
    mut v_x_7577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7578_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_7577_);
    crate::leanh::lean_dec(v_x_7577_);
    return v_res_7578_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry(
    mut v_00_u03b1_7579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7580_: *mut crate::leanh::LeanObject,
    mut v_x_7581_: *mut crate::leanh::LeanObject,
    mut v_x_7582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7583_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_7581_);
    return v___x_7583_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(
    mut v_00_u03b1_7584_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7585_: *mut crate::leanh::LeanObject,
    mut v_x_7586_: *mut crate::leanh::LeanObject,
    mut v_x_7587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7588_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(
        v_00_u03b1_7584_,
        v_00_u03b2_7585_,
        v_x_7586_,
        v_x_7587_,
    );
    crate::leanh::lean_dec(v_x_7586_);
    return v_res_7588_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(
    mut v_x_7589_: *mut crate::leanh::LeanObject,
    mut v_h__1_7590_: *mut crate::leanh::LeanObject,
    mut v_h__2_7591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_7592_ = crate::leanh::lean_ctor_get(v_x_7589_, 3);
    if crate::leanh::lean_obj_tag(v_l_7592_) == 0 {
        let mut v_size_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_7592_);
        crate::leanh::lean_dec(v_h__1_7590_);
        v_size_7593_ = crate::leanh::lean_ctor_get(v_x_7589_, 0);
        crate::leanh::lean_inc(v_size_7593_);
        v_k_7594_ = crate::leanh::lean_ctor_get(v_x_7589_, 1);
        crate::leanh::lean_inc(v_k_7594_);
        v_v_7595_ = crate::leanh::lean_ctor_get(v_x_7589_, 2);
        crate::leanh::lean_inc(v_v_7595_);
        v_r_7596_ = crate::leanh::lean_ctor_get(v_x_7589_, 4);
        crate::leanh::lean_inc(v_r_7596_);
        crate::leanh::lean_dec(v_x_7589_);
        v_size_7597_ = crate::leanh::lean_ctor_get(v_l_7592_, 0);
        crate::leanh::lean_inc(v_size_7597_);
        v_k_7598_ = crate::leanh::lean_ctor_get(v_l_7592_, 1);
        crate::leanh::lean_inc(v_k_7598_);
        v_v_7599_ = crate::leanh::lean_ctor_get(v_l_7592_, 2);
        crate::leanh::lean_inc(v_v_7599_);
        v_l_7600_ = crate::leanh::lean_ctor_get(v_l_7592_, 3);
        crate::leanh::lean_inc(v_l_7600_);
        v_r_7601_ = crate::leanh::lean_ctor_get(v_l_7592_, 4);
        crate::leanh::lean_inc(v_r_7601_);
        crate::leanh::lean_dec_ref_known(v_l_7592_, 5);
        v___x_7602_ = crate::leanh::lean_apply_10(
            v_h__2_7591_,
            v_size_7593_,
            v_k_7594_,
            v_v_7595_,
            v_size_7597_,
            v_k_7598_,
            v_v_7599_,
            v_l_7600_,
            v_r_7601_,
            v_r_7596_,
            crate::leanh::lean_box(0),
        );
        return v___x_7602_;
    } else {
        let mut v_size_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7591_);
        v_size_7603_ = crate::leanh::lean_ctor_get(v_x_7589_, 0);
        crate::leanh::lean_inc(v_size_7603_);
        v_k_7604_ = crate::leanh::lean_ctor_get(v_x_7589_, 1);
        crate::leanh::lean_inc(v_k_7604_);
        v_v_7605_ = crate::leanh::lean_ctor_get(v_x_7589_, 2);
        crate::leanh::lean_inc(v_v_7605_);
        v_r_7606_ = crate::leanh::lean_ctor_get(v_x_7589_, 4);
        crate::leanh::lean_inc(v_r_7606_);
        crate::leanh::lean_dec(v_x_7589_);
        v___x_7607_ = crate::leanh::lean_apply_5(
            v_h__1_7590_,
            v_size_7603_,
            v_k_7604_,
            v_v_7605_,
            v_r_7606_,
            crate::leanh::lean_box(0),
        );
        return v___x_7607_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(
    mut v_00_u03b1_7608_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7609_: *mut crate::leanh::LeanObject,
    mut v_motive_7610_: *mut crate::leanh::LeanObject,
    mut v_x_7611_: *mut crate::leanh::LeanObject,
    mut v_x_7612_: *mut crate::leanh::LeanObject,
    mut v_h__1_7613_: *mut crate::leanh::LeanObject,
    mut v_h__2_7614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_l_7615_ = crate::leanh::lean_ctor_get(v_x_7611_, 3);
    if crate::leanh::lean_obj_tag(v_l_7615_) == 0 {
        let mut v_size_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_l_7615_);
        crate::leanh::lean_dec(v_h__1_7613_);
        v_size_7616_ = crate::leanh::lean_ctor_get(v_x_7611_, 0);
        crate::leanh::lean_inc(v_size_7616_);
        v_k_7617_ = crate::leanh::lean_ctor_get(v_x_7611_, 1);
        crate::leanh::lean_inc(v_k_7617_);
        v_v_7618_ = crate::leanh::lean_ctor_get(v_x_7611_, 2);
        crate::leanh::lean_inc(v_v_7618_);
        v_r_7619_ = crate::leanh::lean_ctor_get(v_x_7611_, 4);
        crate::leanh::lean_inc(v_r_7619_);
        crate::leanh::lean_dec(v_x_7611_);
        v_size_7620_ = crate::leanh::lean_ctor_get(v_l_7615_, 0);
        crate::leanh::lean_inc(v_size_7620_);
        v_k_7621_ = crate::leanh::lean_ctor_get(v_l_7615_, 1);
        crate::leanh::lean_inc(v_k_7621_);
        v_v_7622_ = crate::leanh::lean_ctor_get(v_l_7615_, 2);
        crate::leanh::lean_inc(v_v_7622_);
        v_l_7623_ = crate::leanh::lean_ctor_get(v_l_7615_, 3);
        crate::leanh::lean_inc(v_l_7623_);
        v_r_7624_ = crate::leanh::lean_ctor_get(v_l_7615_, 4);
        crate::leanh::lean_inc(v_r_7624_);
        crate::leanh::lean_dec_ref_known(v_l_7615_, 5);
        v___x_7625_ = crate::leanh::lean_apply_10(
            v_h__2_7614_,
            v_size_7616_,
            v_k_7617_,
            v_v_7618_,
            v_size_7620_,
            v_k_7621_,
            v_v_7622_,
            v_l_7623_,
            v_r_7624_,
            v_r_7619_,
            crate::leanh::lean_box(0),
        );
        return v___x_7625_;
    } else {
        let mut v_size_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7614_);
        v_size_7626_ = crate::leanh::lean_ctor_get(v_x_7611_, 0);
        crate::leanh::lean_inc(v_size_7626_);
        v_k_7627_ = crate::leanh::lean_ctor_get(v_x_7611_, 1);
        crate::leanh::lean_inc(v_k_7627_);
        v_v_7628_ = crate::leanh::lean_ctor_get(v_x_7611_, 2);
        crate::leanh::lean_inc(v_v_7628_);
        v_r_7629_ = crate::leanh::lean_ctor_get(v_x_7611_, 4);
        crate::leanh::lean_inc(v_r_7629_);
        crate::leanh::lean_dec(v_x_7611_);
        v___x_7630_ = crate::leanh::lean_apply_5(
            v_h__1_7613_,
            v_size_7626_,
            v_k_7627_,
            v_v_7628_,
            v_r_7629_,
            crate::leanh::lean_box(0),
        );
        return v___x_7630_;
    }
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7632_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_7633_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_7634_ = crate::leanh::lean_unsigned_to_nat(816);
    v___x_7635_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0;
    v___x_7636_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_7637_ = l_mkPanicMessageWithDecl(
        v___x_7636_,
        v___x_7635_,
        v___x_7634_,
        v___x_7633_,
        v___x_7632_,
    );
    return v___x_7637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(
    mut v_inst_7638_: *mut crate::leanh::LeanObject,
    mut v_x_7639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7639_) == 0 {
                    v_l_7640_ = crate::leanh::lean_ctor_get(v_x_7639_, 3);
                    if crate::leanh::lean_obj_tag(v_l_7640_) == 0 {
                        v_x_7639_ = v_l_7640_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7642_ = crate::leanh::lean_ctor_get(v_x_7639_, 1);
                        v_v_7643_ = crate::leanh::lean_ctor_get(v_x_7639_, 2);
                        crate::leanh::lean_inc(v_v_7643_);
                        crate::leanh::lean_inc(v_k_7642_);
                        v___x_7644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7644_, 0, v_k_7642_);
                        crate::leanh::lean_ctor_set(v___x_7644_, 1, v_v_7643_);
                        return v___x_7644_;
                    }
                } else {
                    v___x_7645_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
                    v___x_7646_ = l_panic___redArg(v_inst_7638_, v___x_7645_);
                    return v___x_7646_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(
    mut v_inst_7647_: *mut crate::leanh::LeanObject,
    mut v_x_7648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7649_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_7647_, v_x_7648_);
    crate::leanh::lean_dec(v_x_7648_);
    crate::leanh::lean_dec_ref(v_inst_7647_);
    return v_res_7649_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(
    mut v_00_u03b1_7650_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7651_: *mut crate::leanh::LeanObject,
    mut v_inst_7652_: *mut crate::leanh::LeanObject,
    mut v_x_7653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7654_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_7652_, v_x_7653_);
    return v___x_7654_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(
    mut v_00_u03b1_7655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7656_: *mut crate::leanh::LeanObject,
    mut v_inst_7657_: *mut crate::leanh::LeanObject,
    mut v_x_7658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7659_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(
        v_00_u03b1_7655_,
        v_00_u03b2_7656_,
        v_inst_7657_,
        v_x_7658_,
    );
    crate::leanh::lean_dec(v_x_7658_);
    crate::leanh::lean_dec_ref(v_inst_7657_);
    return v_res_7659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(
    mut v_x_7660_: *mut crate::leanh::LeanObject,
    mut v_x_7661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7660_) == 0 {
                    v_l_7662_ = crate::leanh::lean_ctor_get(v_x_7660_, 3);
                    if crate::leanh::lean_obj_tag(v_l_7662_) == 0 {
                        v_x_7660_ = v_l_7662_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7664_ = crate::leanh::lean_ctor_get(v_x_7660_, 1);
                        v_v_7665_ = crate::leanh::lean_ctor_get(v_x_7660_, 2);
                        crate::leanh::lean_inc(v_v_7665_);
                        crate::leanh::lean_inc(v_k_7664_);
                        v___x_7666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7666_, 0, v_k_7664_);
                        crate::leanh::lean_ctor_set(v___x_7666_, 1, v_v_7665_);
                        return v___x_7666_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_x_7661_);
                    return v_x_7661_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(
    mut v_x_7667_: *mut crate::leanh::LeanObject,
    mut v_x_7668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7669_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_7667_, v_x_7668_);
    crate::leanh::lean_dec_ref(v_x_7668_);
    crate::leanh::lean_dec(v_x_7667_);
    return v_res_7669_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntryD(
    mut v_00_u03b1_7670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7671_: *mut crate::leanh::LeanObject,
    mut v_x_7672_: *mut crate::leanh::LeanObject,
    mut v_x_7673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7674_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_7672_, v_x_7673_);
    return v___x_7674_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(
    mut v_00_u03b1_7675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7676_: *mut crate::leanh::LeanObject,
    mut v_x_7677_: *mut crate::leanh::LeanObject,
    mut v_x_7678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7679_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(
        v_00_u03b1_7675_,
        v_00_u03b2_7676_,
        v_x_7677_,
        v_x_7678_,
    );
    crate::leanh::lean_dec_ref(v_x_7678_);
    crate::leanh::lean_dec(v_x_7677_);
    return v_res_7679_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(
    mut v_x_7680_: *mut crate::leanh::LeanObject,
    mut v_x_7681_: *mut crate::leanh::LeanObject,
    mut v_h__1_7682_: *mut crate::leanh::LeanObject,
    mut v_h__2_7683_: *mut crate::leanh::LeanObject,
    mut v_h__3_7684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7680_) == 0 {
        let mut v_l_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7682_);
        v_l_7685_ = crate::leanh::lean_ctor_get(v_x_7680_, 3);
        if crate::leanh::lean_obj_tag(v_l_7685_) == 0 {
            let mut v_size_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_7685_);
            crate::leanh::lean_dec(v_h__2_7683_);
            v_size_7686_ = crate::leanh::lean_ctor_get(v_x_7680_, 0);
            crate::leanh::lean_inc(v_size_7686_);
            v_k_7687_ = crate::leanh::lean_ctor_get(v_x_7680_, 1);
            crate::leanh::lean_inc(v_k_7687_);
            v_v_7688_ = crate::leanh::lean_ctor_get(v_x_7680_, 2);
            crate::leanh::lean_inc(v_v_7688_);
            v_r_7689_ = crate::leanh::lean_ctor_get(v_x_7680_, 4);
            crate::leanh::lean_inc(v_r_7689_);
            crate::leanh::lean_dec_ref_known(v_x_7680_, 5);
            v_size_7690_ = crate::leanh::lean_ctor_get(v_l_7685_, 0);
            crate::leanh::lean_inc(v_size_7690_);
            v_k_7691_ = crate::leanh::lean_ctor_get(v_l_7685_, 1);
            crate::leanh::lean_inc(v_k_7691_);
            v_v_7692_ = crate::leanh::lean_ctor_get(v_l_7685_, 2);
            crate::leanh::lean_inc(v_v_7692_);
            v_l_7693_ = crate::leanh::lean_ctor_get(v_l_7685_, 3);
            crate::leanh::lean_inc(v_l_7693_);
            v_r_7694_ = crate::leanh::lean_ctor_get(v_l_7685_, 4);
            crate::leanh::lean_inc(v_r_7694_);
            crate::leanh::lean_dec_ref_known(v_l_7685_, 5);
            v___x_7695_ = crate::leanh::lean_apply_10(
                v_h__3_7684_,
                v_size_7686_,
                v_k_7687_,
                v_v_7688_,
                v_size_7690_,
                v_k_7691_,
                v_v_7692_,
                v_l_7693_,
                v_r_7694_,
                v_r_7689_,
                v_x_7681_,
            );
            return v___x_7695_;
        } else {
            let mut v_size_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7684_);
            v_size_7696_ = crate::leanh::lean_ctor_get(v_x_7680_, 0);
            crate::leanh::lean_inc(v_size_7696_);
            v_k_7697_ = crate::leanh::lean_ctor_get(v_x_7680_, 1);
            crate::leanh::lean_inc(v_k_7697_);
            v_v_7698_ = crate::leanh::lean_ctor_get(v_x_7680_, 2);
            crate::leanh::lean_inc(v_v_7698_);
            v_r_7699_ = crate::leanh::lean_ctor_get(v_x_7680_, 4);
            crate::leanh::lean_inc(v_r_7699_);
            crate::leanh::lean_dec_ref_known(v_x_7680_, 5);
            v___x_7700_ = crate::leanh::lean_apply_5(
                v_h__2_7683_,
                v_size_7696_,
                v_k_7697_,
                v_v_7698_,
                v_r_7699_,
                v_x_7681_,
            );
            return v___x_7700_;
        }
    } else {
        let mut v___x_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7684_);
        crate::leanh::lean_dec(v_h__2_7683_);
        v___x_7701_ = crate::leanh::lean_apply_1(v_h__1_7682_, v_x_7681_);
        return v___x_7701_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(
    mut v_00_u03b1_7702_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7703_: *mut crate::leanh::LeanObject,
    mut v_motive_7704_: *mut crate::leanh::LeanObject,
    mut v_x_7705_: *mut crate::leanh::LeanObject,
    mut v_x_7706_: *mut crate::leanh::LeanObject,
    mut v_h__1_7707_: *mut crate::leanh::LeanObject,
    mut v_h__2_7708_: *mut crate::leanh::LeanObject,
    mut v_h__3_7709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7705_) == 0 {
        let mut v_l_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7707_);
        v_l_7710_ = crate::leanh::lean_ctor_get(v_x_7705_, 3);
        if crate::leanh::lean_obj_tag(v_l_7710_) == 0 {
            let mut v_size_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_l_7710_);
            crate::leanh::lean_dec(v_h__2_7708_);
            v_size_7711_ = crate::leanh::lean_ctor_get(v_x_7705_, 0);
            crate::leanh::lean_inc(v_size_7711_);
            v_k_7712_ = crate::leanh::lean_ctor_get(v_x_7705_, 1);
            crate::leanh::lean_inc(v_k_7712_);
            v_v_7713_ = crate::leanh::lean_ctor_get(v_x_7705_, 2);
            crate::leanh::lean_inc(v_v_7713_);
            v_r_7714_ = crate::leanh::lean_ctor_get(v_x_7705_, 4);
            crate::leanh::lean_inc(v_r_7714_);
            crate::leanh::lean_dec_ref_known(v_x_7705_, 5);
            v_size_7715_ = crate::leanh::lean_ctor_get(v_l_7710_, 0);
            crate::leanh::lean_inc(v_size_7715_);
            v_k_7716_ = crate::leanh::lean_ctor_get(v_l_7710_, 1);
            crate::leanh::lean_inc(v_k_7716_);
            v_v_7717_ = crate::leanh::lean_ctor_get(v_l_7710_, 2);
            crate::leanh::lean_inc(v_v_7717_);
            v_l_7718_ = crate::leanh::lean_ctor_get(v_l_7710_, 3);
            crate::leanh::lean_inc(v_l_7718_);
            v_r_7719_ = crate::leanh::lean_ctor_get(v_l_7710_, 4);
            crate::leanh::lean_inc(v_r_7719_);
            crate::leanh::lean_dec_ref_known(v_l_7710_, 5);
            v___x_7720_ = crate::leanh::lean_apply_10(
                v_h__3_7709_,
                v_size_7711_,
                v_k_7712_,
                v_v_7713_,
                v_size_7715_,
                v_k_7716_,
                v_v_7717_,
                v_l_7718_,
                v_r_7719_,
                v_r_7714_,
                v_x_7706_,
            );
            return v___x_7720_;
        } else {
            let mut v_size_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7709_);
            v_size_7721_ = crate::leanh::lean_ctor_get(v_x_7705_, 0);
            crate::leanh::lean_inc(v_size_7721_);
            v_k_7722_ = crate::leanh::lean_ctor_get(v_x_7705_, 1);
            crate::leanh::lean_inc(v_k_7722_);
            v_v_7723_ = crate::leanh::lean_ctor_get(v_x_7705_, 2);
            crate::leanh::lean_inc(v_v_7723_);
            v_r_7724_ = crate::leanh::lean_ctor_get(v_x_7705_, 4);
            crate::leanh::lean_inc(v_r_7724_);
            crate::leanh::lean_dec_ref_known(v_x_7705_, 5);
            v___x_7725_ = crate::leanh::lean_apply_5(
                v_h__2_7708_,
                v_size_7721_,
                v_k_7722_,
                v_v_7723_,
                v_r_7724_,
                v_x_7706_,
            );
            return v___x_7725_;
        }
    } else {
        let mut v___x_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7709_);
        crate::leanh::lean_dec(v_h__2_7708_);
        v___x_7726_ = crate::leanh::lean_apply_1(v_h__1_7707_, v_x_7706_);
        return v___x_7726_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(
    mut v_x_7727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7727_) == 0 {
                    v_r_7728_ = crate::leanh::lean_ctor_get(v_x_7727_, 4);
                    if crate::leanh::lean_obj_tag(v_r_7728_) == 0 {
                        v_x_7727_ = v_r_7728_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7730_ = crate::leanh::lean_ctor_get(v_x_7727_, 1);
                        v_v_7731_ = crate::leanh::lean_ctor_get(v_x_7727_, 2);
                        crate::leanh::lean_inc(v_v_7731_);
                        crate::leanh::lean_inc(v_k_7730_);
                        v___x_7732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7732_, 0, v_k_7730_);
                        crate::leanh::lean_ctor_set(v___x_7732_, 1, v_v_7731_);
                        v___x_7733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7733_, 0, v___x_7732_);
                        return v___x_7733_;
                    }
                } else {
                    v___x_7734_ = crate::leanh::lean_box(0);
                    return v___x_7734_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(
    mut v_x_7735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7736_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_7735_);
    crate::leanh::lean_dec(v_x_7735_);
    return v_res_7736_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(
    mut v_00_u03b1_7737_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7738_: *mut crate::leanh::LeanObject,
    mut v_x_7739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7740_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_7739_);
    return v___x_7740_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(
    mut v_00_u03b1_7741_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7742_: *mut crate::leanh::LeanObject,
    mut v_x_7743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7744_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(
        v_00_u03b1_7741_,
        v_00_u03b2_7742_,
        v_x_7743_,
    );
    crate::leanh::lean_dec(v_x_7743_);
    return v_res_7744_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(
    mut v_x_7745_: *mut crate::leanh::LeanObject,
    mut v_h__1_7746_: *mut crate::leanh::LeanObject,
    mut v_h__2_7747_: *mut crate::leanh::LeanObject,
    mut v_h__3_7748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7745_) == 0 {
        let mut v_r_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7746_);
        v_r_7749_ = crate::leanh::lean_ctor_get(v_x_7745_, 4);
        if crate::leanh::lean_obj_tag(v_r_7749_) == 0 {
            let mut v_size_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_7749_);
            crate::leanh::lean_dec(v_h__2_7747_);
            v_size_7750_ = crate::leanh::lean_ctor_get(v_x_7745_, 0);
            crate::leanh::lean_inc(v_size_7750_);
            v_k_7751_ = crate::leanh::lean_ctor_get(v_x_7745_, 1);
            crate::leanh::lean_inc(v_k_7751_);
            v_v_7752_ = crate::leanh::lean_ctor_get(v_x_7745_, 2);
            crate::leanh::lean_inc(v_v_7752_);
            v_l_7753_ = crate::leanh::lean_ctor_get(v_x_7745_, 3);
            crate::leanh::lean_inc(v_l_7753_);
            crate::leanh::lean_dec_ref_known(v_x_7745_, 5);
            v_size_7754_ = crate::leanh::lean_ctor_get(v_r_7749_, 0);
            crate::leanh::lean_inc(v_size_7754_);
            v_k_7755_ = crate::leanh::lean_ctor_get(v_r_7749_, 1);
            crate::leanh::lean_inc(v_k_7755_);
            v_v_7756_ = crate::leanh::lean_ctor_get(v_r_7749_, 2);
            crate::leanh::lean_inc(v_v_7756_);
            v_l_7757_ = crate::leanh::lean_ctor_get(v_r_7749_, 3);
            crate::leanh::lean_inc(v_l_7757_);
            v_r_7758_ = crate::leanh::lean_ctor_get(v_r_7749_, 4);
            crate::leanh::lean_inc(v_r_7758_);
            crate::leanh::lean_dec_ref_known(v_r_7749_, 5);
            v___x_7759_ = crate::leanh::lean_apply_9(
                v_h__3_7748_,
                v_size_7750_,
                v_k_7751_,
                v_v_7752_,
                v_l_7753_,
                v_size_7754_,
                v_k_7755_,
                v_v_7756_,
                v_l_7757_,
                v_r_7758_,
            );
            return v___x_7759_;
        } else {
            let mut v_size_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7748_);
            v_size_7760_ = crate::leanh::lean_ctor_get(v_x_7745_, 0);
            crate::leanh::lean_inc(v_size_7760_);
            v_k_7761_ = crate::leanh::lean_ctor_get(v_x_7745_, 1);
            crate::leanh::lean_inc(v_k_7761_);
            v_v_7762_ = crate::leanh::lean_ctor_get(v_x_7745_, 2);
            crate::leanh::lean_inc(v_v_7762_);
            v_l_7763_ = crate::leanh::lean_ctor_get(v_x_7745_, 3);
            crate::leanh::lean_inc(v_l_7763_);
            crate::leanh::lean_dec_ref_known(v_x_7745_, 5);
            v___x_7764_ = crate::leanh::lean_apply_4(
                v_h__2_7747_,
                v_size_7760_,
                v_k_7761_,
                v_v_7762_,
                v_l_7763_,
            );
            return v___x_7764_;
        }
    } else {
        let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7748_);
        crate::leanh::lean_dec(v_h__2_7747_);
        v___x_7765_ = crate::leanh::lean_box(0);
        v___x_7766_ = crate::leanh::lean_apply_1(v_h__1_7746_, v___x_7765_);
        return v___x_7766_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(
    mut v_00_u03b1_7767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7768_: *mut crate::leanh::LeanObject,
    mut v_motive_7769_: *mut crate::leanh::LeanObject,
    mut v_x_7770_: *mut crate::leanh::LeanObject,
    mut v_h__1_7771_: *mut crate::leanh::LeanObject,
    mut v_h__2_7772_: *mut crate::leanh::LeanObject,
    mut v_h__3_7773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7770_) == 0 {
        let mut v_r_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7771_);
        v_r_7774_ = crate::leanh::lean_ctor_get(v_x_7770_, 4);
        if crate::leanh::lean_obj_tag(v_r_7774_) == 0 {
            let mut v_size_7775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_7774_);
            crate::leanh::lean_dec(v_h__2_7772_);
            v_size_7775_ = crate::leanh::lean_ctor_get(v_x_7770_, 0);
            crate::leanh::lean_inc(v_size_7775_);
            v_k_7776_ = crate::leanh::lean_ctor_get(v_x_7770_, 1);
            crate::leanh::lean_inc(v_k_7776_);
            v_v_7777_ = crate::leanh::lean_ctor_get(v_x_7770_, 2);
            crate::leanh::lean_inc(v_v_7777_);
            v_l_7778_ = crate::leanh::lean_ctor_get(v_x_7770_, 3);
            crate::leanh::lean_inc(v_l_7778_);
            crate::leanh::lean_dec_ref_known(v_x_7770_, 5);
            v_size_7779_ = crate::leanh::lean_ctor_get(v_r_7774_, 0);
            crate::leanh::lean_inc(v_size_7779_);
            v_k_7780_ = crate::leanh::lean_ctor_get(v_r_7774_, 1);
            crate::leanh::lean_inc(v_k_7780_);
            v_v_7781_ = crate::leanh::lean_ctor_get(v_r_7774_, 2);
            crate::leanh::lean_inc(v_v_7781_);
            v_l_7782_ = crate::leanh::lean_ctor_get(v_r_7774_, 3);
            crate::leanh::lean_inc(v_l_7782_);
            v_r_7783_ = crate::leanh::lean_ctor_get(v_r_7774_, 4);
            crate::leanh::lean_inc(v_r_7783_);
            crate::leanh::lean_dec_ref_known(v_r_7774_, 5);
            v___x_7784_ = crate::leanh::lean_apply_9(
                v_h__3_7773_,
                v_size_7775_,
                v_k_7776_,
                v_v_7777_,
                v_l_7778_,
                v_size_7779_,
                v_k_7780_,
                v_v_7781_,
                v_l_7782_,
                v_r_7783_,
            );
            return v___x_7784_;
        } else {
            let mut v_size_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7773_);
            v_size_7785_ = crate::leanh::lean_ctor_get(v_x_7770_, 0);
            crate::leanh::lean_inc(v_size_7785_);
            v_k_7786_ = crate::leanh::lean_ctor_get(v_x_7770_, 1);
            crate::leanh::lean_inc(v_k_7786_);
            v_v_7787_ = crate::leanh::lean_ctor_get(v_x_7770_, 2);
            crate::leanh::lean_inc(v_v_7787_);
            v_l_7788_ = crate::leanh::lean_ctor_get(v_x_7770_, 3);
            crate::leanh::lean_inc(v_l_7788_);
            crate::leanh::lean_dec_ref_known(v_x_7770_, 5);
            v___x_7789_ = crate::leanh::lean_apply_4(
                v_h__2_7772_,
                v_size_7785_,
                v_k_7786_,
                v_v_7787_,
                v_l_7788_,
            );
            return v___x_7789_;
        }
    } else {
        let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7773_);
        crate::leanh::lean_dec(v_h__2_7772_);
        v___x_7790_ = crate::leanh::lean_box(0);
        v___x_7791_ = crate::leanh::lean_apply_1(v_h__1_7771_, v___x_7790_);
        return v___x_7791_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(
    mut v_x_7792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_7793_ = crate::leanh::lean_ctor_get(v_x_7792_, 4);
                if crate::leanh::lean_obj_tag(v_r_7793_) == 0 {
                    v_x_7792_ = v_r_7793_;
                    state = 0;
                    continue;
                } else {
                    v_k_7795_ = crate::leanh::lean_ctor_get(v_x_7792_, 1);
                    v_v_7796_ = crate::leanh::lean_ctor_get(v_x_7792_, 2);
                    crate::leanh::lean_inc(v_v_7796_);
                    crate::leanh::lean_inc(v_k_7795_);
                    v___x_7797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7797_, 0, v_k_7795_);
                    crate::leanh::lean_ctor_set(v___x_7797_, 1, v_v_7796_);
                    return v___x_7797_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(
    mut v_x_7798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7799_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_7798_);
    crate::leanh::lean_dec(v_x_7798_);
    return v_res_7799_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry(
    mut v_00_u03b1_7800_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7801_: *mut crate::leanh::LeanObject,
    mut v_x_7802_: *mut crate::leanh::LeanObject,
    mut v_x_7803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7804_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_7802_);
    return v___x_7804_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(
    mut v_00_u03b1_7805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7806_: *mut crate::leanh::LeanObject,
    mut v_x_7807_: *mut crate::leanh::LeanObject,
    mut v_x_7808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7809_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(
        v_00_u03b1_7805_,
        v_00_u03b2_7806_,
        v_x_7807_,
        v_x_7808_,
    );
    crate::leanh::lean_dec(v_x_7807_);
    return v_res_7809_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(
    mut v_x_7810_: *mut crate::leanh::LeanObject,
    mut v_h__1_7811_: *mut crate::leanh::LeanObject,
    mut v_h__2_7812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_7813_ = crate::leanh::lean_ctor_get(v_x_7810_, 4);
    if crate::leanh::lean_obj_tag(v_r_7813_) == 0 {
        let mut v_size_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_7813_);
        crate::leanh::lean_dec(v_h__1_7811_);
        v_size_7814_ = crate::leanh::lean_ctor_get(v_x_7810_, 0);
        crate::leanh::lean_inc(v_size_7814_);
        v_k_7815_ = crate::leanh::lean_ctor_get(v_x_7810_, 1);
        crate::leanh::lean_inc(v_k_7815_);
        v_v_7816_ = crate::leanh::lean_ctor_get(v_x_7810_, 2);
        crate::leanh::lean_inc(v_v_7816_);
        v_l_7817_ = crate::leanh::lean_ctor_get(v_x_7810_, 3);
        crate::leanh::lean_inc(v_l_7817_);
        crate::leanh::lean_dec(v_x_7810_);
        v_size_7818_ = crate::leanh::lean_ctor_get(v_r_7813_, 0);
        crate::leanh::lean_inc(v_size_7818_);
        v_k_7819_ = crate::leanh::lean_ctor_get(v_r_7813_, 1);
        crate::leanh::lean_inc(v_k_7819_);
        v_v_7820_ = crate::leanh::lean_ctor_get(v_r_7813_, 2);
        crate::leanh::lean_inc(v_v_7820_);
        v_l_7821_ = crate::leanh::lean_ctor_get(v_r_7813_, 3);
        crate::leanh::lean_inc(v_l_7821_);
        v_r_7822_ = crate::leanh::lean_ctor_get(v_r_7813_, 4);
        crate::leanh::lean_inc(v_r_7822_);
        crate::leanh::lean_dec_ref_known(v_r_7813_, 5);
        v___x_7823_ = crate::leanh::lean_apply_10(
            v_h__2_7812_,
            v_size_7814_,
            v_k_7815_,
            v_v_7816_,
            v_l_7817_,
            v_size_7818_,
            v_k_7819_,
            v_v_7820_,
            v_l_7821_,
            v_r_7822_,
            crate::leanh::lean_box(0),
        );
        return v___x_7823_;
    } else {
        let mut v_size_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7812_);
        v_size_7824_ = crate::leanh::lean_ctor_get(v_x_7810_, 0);
        crate::leanh::lean_inc(v_size_7824_);
        v_k_7825_ = crate::leanh::lean_ctor_get(v_x_7810_, 1);
        crate::leanh::lean_inc(v_k_7825_);
        v_v_7826_ = crate::leanh::lean_ctor_get(v_x_7810_, 2);
        crate::leanh::lean_inc(v_v_7826_);
        v_l_7827_ = crate::leanh::lean_ctor_get(v_x_7810_, 3);
        crate::leanh::lean_inc(v_l_7827_);
        crate::leanh::lean_dec(v_x_7810_);
        v___x_7828_ = crate::leanh::lean_apply_5(
            v_h__1_7811_,
            v_size_7824_,
            v_k_7825_,
            v_v_7826_,
            v_l_7827_,
            crate::leanh::lean_box(0),
        );
        return v___x_7828_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(
    mut v_00_u03b1_7829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7830_: *mut crate::leanh::LeanObject,
    mut v_motive_7831_: *mut crate::leanh::LeanObject,
    mut v_x_7832_: *mut crate::leanh::LeanObject,
    mut v_x_7833_: *mut crate::leanh::LeanObject,
    mut v_h__1_7834_: *mut crate::leanh::LeanObject,
    mut v_h__2_7835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_7836_ = crate::leanh::lean_ctor_get(v_x_7832_, 4);
    if crate::leanh::lean_obj_tag(v_r_7836_) == 0 {
        let mut v_size_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_7841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_r_7836_);
        crate::leanh::lean_dec(v_h__1_7834_);
        v_size_7837_ = crate::leanh::lean_ctor_get(v_x_7832_, 0);
        crate::leanh::lean_inc(v_size_7837_);
        v_k_7838_ = crate::leanh::lean_ctor_get(v_x_7832_, 1);
        crate::leanh::lean_inc(v_k_7838_);
        v_v_7839_ = crate::leanh::lean_ctor_get(v_x_7832_, 2);
        crate::leanh::lean_inc(v_v_7839_);
        v_l_7840_ = crate::leanh::lean_ctor_get(v_x_7832_, 3);
        crate::leanh::lean_inc(v_l_7840_);
        crate::leanh::lean_dec(v_x_7832_);
        v_size_7841_ = crate::leanh::lean_ctor_get(v_r_7836_, 0);
        crate::leanh::lean_inc(v_size_7841_);
        v_k_7842_ = crate::leanh::lean_ctor_get(v_r_7836_, 1);
        crate::leanh::lean_inc(v_k_7842_);
        v_v_7843_ = crate::leanh::lean_ctor_get(v_r_7836_, 2);
        crate::leanh::lean_inc(v_v_7843_);
        v_l_7844_ = crate::leanh::lean_ctor_get(v_r_7836_, 3);
        crate::leanh::lean_inc(v_l_7844_);
        v_r_7845_ = crate::leanh::lean_ctor_get(v_r_7836_, 4);
        crate::leanh::lean_inc(v_r_7845_);
        crate::leanh::lean_dec_ref_known(v_r_7836_, 5);
        v___x_7846_ = crate::leanh::lean_apply_10(
            v_h__2_7835_,
            v_size_7837_,
            v_k_7838_,
            v_v_7839_,
            v_l_7840_,
            v_size_7841_,
            v_k_7842_,
            v_v_7843_,
            v_l_7844_,
            v_r_7845_,
            crate::leanh::lean_box(0),
        );
        return v___x_7846_;
    } else {
        let mut v_size_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_7835_);
        v_size_7847_ = crate::leanh::lean_ctor_get(v_x_7832_, 0);
        crate::leanh::lean_inc(v_size_7847_);
        v_k_7848_ = crate::leanh::lean_ctor_get(v_x_7832_, 1);
        crate::leanh::lean_inc(v_k_7848_);
        v_v_7849_ = crate::leanh::lean_ctor_get(v_x_7832_, 2);
        crate::leanh::lean_inc(v_v_7849_);
        v_l_7850_ = crate::leanh::lean_ctor_get(v_x_7832_, 3);
        crate::leanh::lean_inc(v_l_7850_);
        crate::leanh::lean_dec(v_x_7832_);
        v___x_7851_ = crate::leanh::lean_apply_5(
            v_h__1_7834_,
            v_size_7847_,
            v_k_7848_,
            v_v_7849_,
            v_l_7850_,
            crate::leanh::lean_box(0),
        );
        return v___x_7851_;
    }
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7853_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1;
    v___x_7854_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_7855_ = crate::leanh::lean_unsigned_to_nat(839);
    v___x_7856_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0;
    v___x_7857_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_7858_ = l_mkPanicMessageWithDecl(
        v___x_7857_,
        v___x_7856_,
        v___x_7855_,
        v___x_7854_,
        v___x_7853_,
    );
    return v___x_7858_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(
    mut v_inst_7859_: *mut crate::leanh::LeanObject,
    mut v_x_7860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7860_) == 0 {
                    v_r_7861_ = crate::leanh::lean_ctor_get(v_x_7860_, 4);
                    if crate::leanh::lean_obj_tag(v_r_7861_) == 0 {
                        v_x_7860_ = v_r_7861_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7863_ = crate::leanh::lean_ctor_get(v_x_7860_, 1);
                        v_v_7864_ = crate::leanh::lean_ctor_get(v_x_7860_, 2);
                        crate::leanh::lean_inc(v_v_7864_);
                        crate::leanh::lean_inc(v_k_7863_);
                        v___x_7865_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7865_, 0, v_k_7863_);
                        crate::leanh::lean_ctor_set(v___x_7865_, 1, v_v_7864_);
                        return v___x_7865_;
                    }
                } else {
                    v___x_7866_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
                    v___x_7867_ = l_panic___redArg(v_inst_7859_, v___x_7866_);
                    return v___x_7867_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(
    mut v_inst_7868_: *mut crate::leanh::LeanObject,
    mut v_x_7869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7870_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_7868_, v_x_7869_);
    crate::leanh::lean_dec(v_x_7869_);
    crate::leanh::lean_dec_ref(v_inst_7868_);
    return v_res_7870_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(
    mut v_00_u03b1_7871_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7872_: *mut crate::leanh::LeanObject,
    mut v_inst_7873_: *mut crate::leanh::LeanObject,
    mut v_x_7874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7875_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_7873_, v_x_7874_);
    return v___x_7875_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(
    mut v_00_u03b1_7876_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7877_: *mut crate::leanh::LeanObject,
    mut v_inst_7878_: *mut crate::leanh::LeanObject,
    mut v_x_7879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7880_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(
        v_00_u03b1_7876_,
        v_00_u03b2_7877_,
        v_inst_7878_,
        v_x_7879_,
    );
    crate::leanh::lean_dec(v_x_7879_);
    crate::leanh::lean_dec_ref(v_inst_7878_);
    return v_res_7880_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(
    mut v_x_7881_: *mut crate::leanh::LeanObject,
    mut v_x_7882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7881_) == 0 {
                    v_r_7883_ = crate::leanh::lean_ctor_get(v_x_7881_, 4);
                    if crate::leanh::lean_obj_tag(v_r_7883_) == 0 {
                        v_x_7881_ = v_r_7883_;
                        state = 0;
                        continue;
                    } else {
                        v_k_7885_ = crate::leanh::lean_ctor_get(v_x_7881_, 1);
                        v_v_7886_ = crate::leanh::lean_ctor_get(v_x_7881_, 2);
                        crate::leanh::lean_inc(v_v_7886_);
                        crate::leanh::lean_inc(v_k_7885_);
                        v___x_7887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7887_, 0, v_k_7885_);
                        crate::leanh::lean_ctor_set(v___x_7887_, 1, v_v_7886_);
                        return v___x_7887_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_x_7882_);
                    return v_x_7882_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(
    mut v_x_7888_: *mut crate::leanh::LeanObject,
    mut v_x_7889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7890_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_7888_, v_x_7889_);
    crate::leanh::lean_dec_ref(v_x_7889_);
    crate::leanh::lean_dec(v_x_7888_);
    return v_res_7890_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(
    mut v_00_u03b1_7891_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7892_: *mut crate::leanh::LeanObject,
    mut v_x_7893_: *mut crate::leanh::LeanObject,
    mut v_x_7894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7895_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_7893_, v_x_7894_);
    return v___x_7895_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(
    mut v_00_u03b1_7896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7897_: *mut crate::leanh::LeanObject,
    mut v_x_7898_: *mut crate::leanh::LeanObject,
    mut v_x_7899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7900_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(
        v_00_u03b1_7896_,
        v_00_u03b2_7897_,
        v_x_7898_,
        v_x_7899_,
    );
    crate::leanh::lean_dec_ref(v_x_7899_);
    crate::leanh::lean_dec(v_x_7898_);
    return v_res_7900_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(
    mut v_x_7901_: *mut crate::leanh::LeanObject,
    mut v_x_7902_: *mut crate::leanh::LeanObject,
    mut v_h__1_7903_: *mut crate::leanh::LeanObject,
    mut v_h__2_7904_: *mut crate::leanh::LeanObject,
    mut v_h__3_7905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7901_) == 0 {
        let mut v_r_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7903_);
        v_r_7906_ = crate::leanh::lean_ctor_get(v_x_7901_, 4);
        if crate::leanh::lean_obj_tag(v_r_7906_) == 0 {
            let mut v_size_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_7906_);
            crate::leanh::lean_dec(v_h__2_7904_);
            v_size_7907_ = crate::leanh::lean_ctor_get(v_x_7901_, 0);
            crate::leanh::lean_inc(v_size_7907_);
            v_k_7908_ = crate::leanh::lean_ctor_get(v_x_7901_, 1);
            crate::leanh::lean_inc(v_k_7908_);
            v_v_7909_ = crate::leanh::lean_ctor_get(v_x_7901_, 2);
            crate::leanh::lean_inc(v_v_7909_);
            v_l_7910_ = crate::leanh::lean_ctor_get(v_x_7901_, 3);
            crate::leanh::lean_inc(v_l_7910_);
            crate::leanh::lean_dec_ref_known(v_x_7901_, 5);
            v_size_7911_ = crate::leanh::lean_ctor_get(v_r_7906_, 0);
            crate::leanh::lean_inc(v_size_7911_);
            v_k_7912_ = crate::leanh::lean_ctor_get(v_r_7906_, 1);
            crate::leanh::lean_inc(v_k_7912_);
            v_v_7913_ = crate::leanh::lean_ctor_get(v_r_7906_, 2);
            crate::leanh::lean_inc(v_v_7913_);
            v_l_7914_ = crate::leanh::lean_ctor_get(v_r_7906_, 3);
            crate::leanh::lean_inc(v_l_7914_);
            v_r_7915_ = crate::leanh::lean_ctor_get(v_r_7906_, 4);
            crate::leanh::lean_inc(v_r_7915_);
            crate::leanh::lean_dec_ref_known(v_r_7906_, 5);
            v___x_7916_ = crate::leanh::lean_apply_10(
                v_h__3_7905_,
                v_size_7907_,
                v_k_7908_,
                v_v_7909_,
                v_l_7910_,
                v_size_7911_,
                v_k_7912_,
                v_v_7913_,
                v_l_7914_,
                v_r_7915_,
                v_x_7902_,
            );
            return v___x_7916_;
        } else {
            let mut v_size_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7905_);
            v_size_7917_ = crate::leanh::lean_ctor_get(v_x_7901_, 0);
            crate::leanh::lean_inc(v_size_7917_);
            v_k_7918_ = crate::leanh::lean_ctor_get(v_x_7901_, 1);
            crate::leanh::lean_inc(v_k_7918_);
            v_v_7919_ = crate::leanh::lean_ctor_get(v_x_7901_, 2);
            crate::leanh::lean_inc(v_v_7919_);
            v_l_7920_ = crate::leanh::lean_ctor_get(v_x_7901_, 3);
            crate::leanh::lean_inc(v_l_7920_);
            crate::leanh::lean_dec_ref_known(v_x_7901_, 5);
            v___x_7921_ = crate::leanh::lean_apply_5(
                v_h__2_7904_,
                v_size_7917_,
                v_k_7918_,
                v_v_7919_,
                v_l_7920_,
                v_x_7902_,
            );
            return v___x_7921_;
        }
    } else {
        let mut v___x_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7905_);
        crate::leanh::lean_dec(v_h__2_7904_);
        v___x_7922_ = crate::leanh::lean_apply_1(v_h__1_7903_, v_x_7902_);
        return v___x_7922_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(
    mut v_00_u03b1_7923_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7924_: *mut crate::leanh::LeanObject,
    mut v_motive_7925_: *mut crate::leanh::LeanObject,
    mut v_x_7926_: *mut crate::leanh::LeanObject,
    mut v_x_7927_: *mut crate::leanh::LeanObject,
    mut v_h__1_7928_: *mut crate::leanh::LeanObject,
    mut v_h__2_7929_: *mut crate::leanh::LeanObject,
    mut v_h__3_7930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_7926_) == 0 {
        let mut v_r_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_7928_);
        v_r_7931_ = crate::leanh::lean_ctor_get(v_x_7926_, 4);
        if crate::leanh::lean_obj_tag(v_r_7931_) == 0 {
            let mut v_size_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_size_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_r_7931_);
            crate::leanh::lean_dec(v_h__2_7929_);
            v_size_7932_ = crate::leanh::lean_ctor_get(v_x_7926_, 0);
            crate::leanh::lean_inc(v_size_7932_);
            v_k_7933_ = crate::leanh::lean_ctor_get(v_x_7926_, 1);
            crate::leanh::lean_inc(v_k_7933_);
            v_v_7934_ = crate::leanh::lean_ctor_get(v_x_7926_, 2);
            crate::leanh::lean_inc(v_v_7934_);
            v_l_7935_ = crate::leanh::lean_ctor_get(v_x_7926_, 3);
            crate::leanh::lean_inc(v_l_7935_);
            crate::leanh::lean_dec_ref_known(v_x_7926_, 5);
            v_size_7936_ = crate::leanh::lean_ctor_get(v_r_7931_, 0);
            crate::leanh::lean_inc(v_size_7936_);
            v_k_7937_ = crate::leanh::lean_ctor_get(v_r_7931_, 1);
            crate::leanh::lean_inc(v_k_7937_);
            v_v_7938_ = crate::leanh::lean_ctor_get(v_r_7931_, 2);
            crate::leanh::lean_inc(v_v_7938_);
            v_l_7939_ = crate::leanh::lean_ctor_get(v_r_7931_, 3);
            crate::leanh::lean_inc(v_l_7939_);
            v_r_7940_ = crate::leanh::lean_ctor_get(v_r_7931_, 4);
            crate::leanh::lean_inc(v_r_7940_);
            crate::leanh::lean_dec_ref_known(v_r_7931_, 5);
            v___x_7941_ = crate::leanh::lean_apply_10(
                v_h__3_7930_,
                v_size_7932_,
                v_k_7933_,
                v_v_7934_,
                v_l_7935_,
                v_size_7936_,
                v_k_7937_,
                v_v_7938_,
                v_l_7939_,
                v_r_7940_,
                v_x_7927_,
            );
            return v___x_7941_;
        } else {
            let mut v_size_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_l_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_7930_);
            v_size_7942_ = crate::leanh::lean_ctor_get(v_x_7926_, 0);
            crate::leanh::lean_inc(v_size_7942_);
            v_k_7943_ = crate::leanh::lean_ctor_get(v_x_7926_, 1);
            crate::leanh::lean_inc(v_k_7943_);
            v_v_7944_ = crate::leanh::lean_ctor_get(v_x_7926_, 2);
            crate::leanh::lean_inc(v_v_7944_);
            v_l_7945_ = crate::leanh::lean_ctor_get(v_x_7926_, 3);
            crate::leanh::lean_inc(v_l_7945_);
            crate::leanh::lean_dec_ref_known(v_x_7926_, 5);
            v___x_7946_ = crate::leanh::lean_apply_5(
                v_h__2_7929_,
                v_size_7942_,
                v_k_7943_,
                v_v_7944_,
                v_l_7945_,
                v_x_7927_,
            );
            return v___x_7946_;
        }
    } else {
        let mut v___x_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_7930_);
        crate::leanh::lean_dec(v_h__2_7929_);
        v___x_7947_ = crate::leanh::lean_apply_1(v_h__1_7928_, v_x_7927_);
        return v___x_7947_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(
    mut v_x_7948_: *mut crate::leanh::LeanObject,
    mut v_x_7949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: u8 = 0;
    let mut v___x_7963_: u8 = 0;
    let mut v_size_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_7950_ = crate::leanh::lean_ctor_get(v_x_7948_, 1);
                v_v_7951_ = crate::leanh::lean_ctor_get(v_x_7948_, 2);
                v_l_7952_ = crate::leanh::lean_ctor_get(v_x_7948_, 3);
                v_r_7953_ = crate::leanh::lean_ctor_get(v_x_7948_, 4);
                if crate::leanh::lean_obj_tag(v_l_7952_) == 0 {
                    v_size_7968_ = crate::leanh::lean_ctor_get(v_l_7952_, 0);
                    v___y_7961_ = v_size_7968_;
                    state = 2;
                    continue;
                } else {
                    v___x_7969_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7961_ = v___x_7969_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_7956_ = lean_nat_sub(v_x_7949_, v___y_7955_);
                crate::leanh::lean_dec(v_x_7949_);
                v___x_7957_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7958_ = lean_nat_sub(v___x_7956_, v___x_7957_);
                crate::leanh::lean_dec(v___x_7956_);
                v_x_7948_ = v_r_7953_;
                v_x_7949_ = v___x_7958_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7962_ = lean_nat_dec_lt(v_x_7949_, v___y_7961_);
                if v___x_7962_ == 0 {
                    v___x_7963_ = lean_nat_dec_eq(v_x_7949_, v___y_7961_);
                    if v___x_7963_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_7952_) == 0 {
                            v_size_7964_ = crate::leanh::lean_ctor_get(v_l_7952_, 0);
                            v___y_7955_ = v_size_7964_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7965_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_7955_ = v___x_7965_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_7949_);
                        crate::leanh::lean_inc(v_v_7951_);
                        crate::leanh::lean_inc(v_k_7950_);
                        v___x_7966_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7966_, 0, v_k_7950_);
                        crate::leanh::lean_ctor_set(v___x_7966_, 1, v_v_7951_);
                        return v___x_7966_;
                    }
                } else {
                    v_x_7948_ = v_l_7952_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(
    mut v_x_7970_: *mut crate::leanh::LeanObject,
    mut v_x_7971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7972_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_7970_, v_x_7971_);
    crate::leanh::lean_dec(v_x_7970_);
    return v_res_7972_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(
    mut v_00_u03b1_7973_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7974_: *mut crate::leanh::LeanObject,
    mut v_x_7975_: *mut crate::leanh::LeanObject,
    mut v_x_7976_: *mut crate::leanh::LeanObject,
    mut v_x_7977_: *mut crate::leanh::LeanObject,
    mut v_x_7978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7979_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_7975_, v_x_7977_);
    return v___x_7979_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(
    mut v_00_u03b1_7980_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7981_: *mut crate::leanh::LeanObject,
    mut v_x_7982_: *mut crate::leanh::LeanObject,
    mut v_x_7983_: *mut crate::leanh::LeanObject,
    mut v_x_7984_: *mut crate::leanh::LeanObject,
    mut v_x_7985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7986_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(
        v_00_u03b1_7980_,
        v_00_u03b2_7981_,
        v_x_7982_,
        v_x_7983_,
        v_x_7984_,
        v_x_7985_,
    );
    crate::leanh::lean_dec(v_x_7982_);
    return v_res_7986_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(
    mut v_x_7987_: *mut crate::leanh::LeanObject,
    mut v_x_7988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: u8 = 0;
    let mut v___x_8002_: u8 = 0;
    let mut v_size_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7987_) == 0 {
                    v_k_7989_ = crate::leanh::lean_ctor_get(v_x_7987_, 1);
                    v_v_7990_ = crate::leanh::lean_ctor_get(v_x_7987_, 2);
                    v_l_7991_ = crate::leanh::lean_ctor_get(v_x_7987_, 3);
                    v_r_7992_ = crate::leanh::lean_ctor_get(v_x_7987_, 4);
                    if crate::leanh::lean_obj_tag(v_l_7991_) == 0 {
                        v_size_8008_ = crate::leanh::lean_ctor_get(v_l_7991_, 0);
                        v___y_8000_ = v_size_8008_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8009_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_8000_ = v___x_8009_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_7988_);
                    v___x_8010_ = crate::leanh::lean_box(0);
                    return v___x_8010_;
                }
            }
            1 => {
                v___x_7995_ = lean_nat_sub(v_x_7988_, v___y_7994_);
                crate::leanh::lean_dec(v_x_7988_);
                v___x_7996_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7997_ = lean_nat_sub(v___x_7995_, v___x_7996_);
                crate::leanh::lean_dec(v___x_7995_);
                v_x_7987_ = v_r_7992_;
                v_x_7988_ = v___x_7997_;
                state = 0;
                continue;
            }
            2 => {
                v___x_8001_ = lean_nat_dec_lt(v_x_7988_, v___y_8000_);
                if v___x_8001_ == 0 {
                    v___x_8002_ = lean_nat_dec_eq(v_x_7988_, v___y_8000_);
                    if v___x_8002_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_7991_) == 0 {
                            v_size_8003_ = crate::leanh::lean_ctor_get(v_l_7991_, 0);
                            v___y_7994_ = v_size_8003_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8004_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_7994_ = v___x_8004_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_7988_);
                        crate::leanh::lean_inc(v_v_7990_);
                        crate::leanh::lean_inc(v_k_7989_);
                        v___x_8005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8005_, 0, v_k_7989_);
                        crate::leanh::lean_ctor_set(v___x_8005_, 1, v_v_7990_);
                        v___x_8006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8006_, 0, v___x_8005_);
                        return v___x_8006_;
                    }
                } else {
                    v_x_7987_ = v_l_7991_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(
    mut v_x_8011_: *mut crate::leanh::LeanObject,
    mut v_x_8012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8013_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_8011_, v_x_8012_);
    crate::leanh::lean_dec(v_x_8011_);
    return v_res_8013_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(
    mut v_00_u03b1_8014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8015_: *mut crate::leanh::LeanObject,
    mut v_x_8016_: *mut crate::leanh::LeanObject,
    mut v_x_8017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8018_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_8016_, v_x_8017_);
    return v___x_8018_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(
    mut v_00_u03b1_8019_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8020_: *mut crate::leanh::LeanObject,
    mut v_x_8021_: *mut crate::leanh::LeanObject,
    mut v_x_8022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8023_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(
        v_00_u03b1_8019_,
        v_00_u03b2_8020_,
        v_x_8021_,
        v_x_8022_,
    );
    crate::leanh::lean_dec(v_x_8021_);
    return v_res_8023_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8025_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1;
    v___x_8026_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_8027_ = crate::leanh::lean_unsigned_to_nat(870);
    v___x_8028_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0;
    v___x_8029_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0;
    v___x_8030_ = l_mkPanicMessageWithDecl(
        v___x_8029_,
        v___x_8028_,
        v___x_8027_,
        v___x_8026_,
        v___x_8025_,
    );
    return v___x_8030_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
    mut v_inst_8031_: *mut crate::leanh::LeanObject,
    mut v_x_8032_: *mut crate::leanh::LeanObject,
    mut v_x_8033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8046_: u8 = 0;
    let mut v___x_8047_: u8 = 0;
    let mut v_size_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8032_) == 0 {
                    v_k_8034_ = crate::leanh::lean_ctor_get(v_x_8032_, 1);
                    v_v_8035_ = crate::leanh::lean_ctor_get(v_x_8032_, 2);
                    v_l_8036_ = crate::leanh::lean_ctor_get(v_x_8032_, 3);
                    v_r_8037_ = crate::leanh::lean_ctor_get(v_x_8032_, 4);
                    if crate::leanh::lean_obj_tag(v_l_8036_) == 0 {
                        v_size_8052_ = crate::leanh::lean_ctor_get(v_l_8036_, 0);
                        v___y_8045_ = v_size_8052_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8053_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_8045_ = v___x_8053_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_8033_);
                    v___x_8054_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
                    v___x_8055_ = l_panic___redArg(v_inst_8031_, v___x_8054_);
                    return v___x_8055_;
                }
            }
            1 => {
                v___x_8040_ = lean_nat_sub(v_x_8033_, v___y_8039_);
                crate::leanh::lean_dec(v_x_8033_);
                v___x_8041_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_8042_ = lean_nat_sub(v___x_8040_, v___x_8041_);
                crate::leanh::lean_dec(v___x_8040_);
                v_x_8032_ = v_r_8037_;
                v_x_8033_ = v___x_8042_;
                state = 0;
                continue;
            }
            2 => {
                v___x_8046_ = lean_nat_dec_lt(v_x_8033_, v___y_8045_);
                if v___x_8046_ == 0 {
                    v___x_8047_ = lean_nat_dec_eq(v_x_8033_, v___y_8045_);
                    if v___x_8047_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_8036_) == 0 {
                            v_size_8048_ = crate::leanh::lean_ctor_get(v_l_8036_, 0);
                            v___y_8039_ = v_size_8048_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8049_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_8039_ = v___x_8049_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_8033_);
                        crate::leanh::lean_inc(v_v_8035_);
                        crate::leanh::lean_inc(v_k_8034_);
                        v___x_8050_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8050_, 0, v_k_8034_);
                        crate::leanh::lean_ctor_set(v___x_8050_, 1, v_v_8035_);
                        return v___x_8050_;
                    }
                } else {
                    v_x_8032_ = v_l_8036_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(
    mut v_inst_8056_: *mut crate::leanh::LeanObject,
    mut v_x_8057_: *mut crate::leanh::LeanObject,
    mut v_x_8058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8059_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_8056_,
        v_x_8057_,
        v_x_8058_,
    );
    crate::leanh::lean_dec(v_x_8057_);
    crate::leanh::lean_dec_ref(v_inst_8056_);
    return v_res_8059_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(
    mut v_00_u03b1_8060_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8061_: *mut crate::leanh::LeanObject,
    mut v_inst_8062_: *mut crate::leanh::LeanObject,
    mut v_x_8063_: *mut crate::leanh::LeanObject,
    mut v_x_8064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8065_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(
        v_inst_8062_,
        v_x_8063_,
        v_x_8064_,
    );
    return v___x_8065_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(
    mut v_00_u03b1_8066_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8067_: *mut crate::leanh::LeanObject,
    mut v_inst_8068_: *mut crate::leanh::LeanObject,
    mut v_x_8069_: *mut crate::leanh::LeanObject,
    mut v_x_8070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8071_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(
        v_00_u03b1_8066_,
        v_00_u03b2_8067_,
        v_inst_8068_,
        v_x_8069_,
        v_x_8070_,
    );
    crate::leanh::lean_dec(v_x_8069_);
    crate::leanh::lean_dec_ref(v_inst_8068_);
    return v_res_8071_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(
    mut v_x_8072_: *mut crate::leanh::LeanObject,
    mut v_x_8073_: *mut crate::leanh::LeanObject,
    mut v_x_8074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8087_: u8 = 0;
    let mut v___x_8088_: u8 = 0;
    let mut v_size_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_8093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_8072_) == 0 {
                    v_k_8075_ = crate::leanh::lean_ctor_get(v_x_8072_, 1);
                    v_v_8076_ = crate::leanh::lean_ctor_get(v_x_8072_, 2);
                    v_l_8077_ = crate::leanh::lean_ctor_get(v_x_8072_, 3);
                    v_r_8078_ = crate::leanh::lean_ctor_get(v_x_8072_, 4);
                    if crate::leanh::lean_obj_tag(v_l_8077_) == 0 {
                        v_size_8093_ = crate::leanh::lean_ctor_get(v_l_8077_, 0);
                        v___y_8086_ = v_size_8093_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8094_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_8086_ = v___x_8094_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_8073_);
                    crate::leanh::lean_inc_ref(v_x_8074_);
                    return v_x_8074_;
                }
            }
            1 => {
                v___x_8081_ = lean_nat_sub(v_x_8073_, v___y_8080_);
                crate::leanh::lean_dec(v_x_8073_);
                v___x_8082_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_8083_ = lean_nat_sub(v___x_8081_, v___x_8082_);
                crate::leanh::lean_dec(v___x_8081_);
                v_x_8072_ = v_r_8078_;
                v_x_8073_ = v___x_8083_;
                state = 0;
                continue;
            }
            2 => {
                v___x_8087_ = lean_nat_dec_lt(v_x_8073_, v___y_8086_);
                if v___x_8087_ == 0 {
                    v___x_8088_ = lean_nat_dec_eq(v_x_8073_, v___y_8086_);
                    if v___x_8088_ == 0 {
                        if crate::leanh::lean_obj_tag(v_l_8077_) == 0 {
                            v_size_8089_ = crate::leanh::lean_ctor_get(v_l_8077_, 0);
                            v___y_8080_ = v_size_8089_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8090_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_8080_ = v___x_8090_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_8073_);
                        crate::leanh::lean_inc(v_v_8076_);
                        crate::leanh::lean_inc(v_k_8075_);
                        v___x_8091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8091_, 0, v_k_8075_);
                        crate::leanh::lean_ctor_set(v___x_8091_, 1, v_v_8076_);
                        return v___x_8091_;
                    }
                } else {
                    v_x_8072_ = v_l_8077_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(
    mut v_x_8095_: *mut crate::leanh::LeanObject,
    mut v_x_8096_: *mut crate::leanh::LeanObject,
    mut v_x_8097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8098_ =
        l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_8095_, v_x_8096_, v_x_8097_);
    crate::leanh::lean_dec_ref(v_x_8097_);
    crate::leanh::lean_dec(v_x_8095_);
    return v_res_8098_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(
    mut v_00_u03b1_8099_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8100_: *mut crate::leanh::LeanObject,
    mut v_x_8101_: *mut crate::leanh::LeanObject,
    mut v_x_8102_: *mut crate::leanh::LeanObject,
    mut v_x_8103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8104_ =
        l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_8101_, v_x_8102_, v_x_8103_);
    return v___x_8104_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(
    mut v_00_u03b1_8105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8106_: *mut crate::leanh::LeanObject,
    mut v_x_8107_: *mut crate::leanh::LeanObject,
    mut v_x_8108_: *mut crate::leanh::LeanObject,
    mut v_x_8109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8110_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(
        v_00_u03b1_8105_,
        v_00_u03b2_8106_,
        v_x_8107_,
        v_x_8108_,
        v_x_8109_,
    );
    crate::leanh::lean_dec_ref(v_x_8109_);
    crate::leanh::lean_dec(v_x_8107_);
    return v_res_8110_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
    mut v_inst_8111_: *mut crate::leanh::LeanObject,
    mut v_k_8112_: *mut crate::leanh::LeanObject,
    mut v_best_8113_: *mut crate::leanh::LeanObject,
    mut v_a_8114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: u8 = 0;
    let mut v___x_8121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_8114_) == 0 {
                    v_k_8115_ = crate::leanh::lean_ctor_get(v_a_8114_, 1);
                    crate::leanh::lean_inc_n(v_k_8115_, 2);
                    v_v_8116_ = crate::leanh::lean_ctor_get(v_a_8114_, 2);
                    crate::leanh::lean_inc(v_v_8116_);
                    v_l_8117_ = crate::leanh::lean_ctor_get(v_a_8114_, 3);
                    crate::leanh::lean_inc(v_l_8117_);
                    v_r_8118_ = crate::leanh::lean_ctor_get(v_a_8114_, 4);
                    crate::leanh::lean_inc(v_r_8118_);
                    crate::leanh::lean_dec_ref_known(v_a_8114_, 5);
                    crate::leanh::lean_inc_ref(v_inst_8111_);
                    crate::leanh::lean_inc(v_k_8112_);
                    v___x_8119_ = crate::leanh::lean_apply_2(v_inst_8111_, v_k_8112_, v_k_8115_);
                    v___x_8120_ = (crate::leanh::lean_unbox(v___x_8119_) as u8);
                    match v___x_8120_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_8118_);
                            crate::leanh::lean_dec(v_best_8113_);
                            v___x_8121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8121_, 0, v_k_8115_);
                            crate::leanh::lean_ctor_set(v___x_8121_, 1, v_v_8116_);
                            v___x_8122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8122_, 0, v___x_8121_);
                            v_best_8113_ = v___x_8122_;
                            v_a_8114_ = v_l_8117_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_8118_);
                            crate::leanh::lean_dec(v_l_8117_);
                            crate::leanh::lean_dec(v_best_8113_);
                            crate::leanh::lean_dec(v_k_8112_);
                            crate::leanh::lean_dec_ref(v_inst_8111_);
                            v___x_8124_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8124_, 0, v_k_8115_);
                            crate::leanh::lean_ctor_set(v___x_8124_, 1, v_v_8116_);
                            v___x_8125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8125_, 0, v___x_8124_);
                            return v___x_8125_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_8117_);
                            crate::leanh::lean_dec(v_v_8116_);
                            crate::leanh::lean_dec(v_k_8115_);
                            v_a_8114_ = v_r_8118_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8112_);
                    crate::leanh::lean_dec_ref(v_inst_8111_);
                    return v_best_8113_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(
    mut v_00_u03b1_8127_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8128_: *mut crate::leanh::LeanObject,
    mut v_inst_8129_: *mut crate::leanh::LeanObject,
    mut v_k_8130_: *mut crate::leanh::LeanObject,
    mut v_best_8131_: *mut crate::leanh::LeanObject,
    mut v_a_8132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8133_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8129_,
        v_k_8130_,
        v_best_8131_,
        v_a_8132_,
    );
    return v___x_8133_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(
    mut v_inst_8134_: *mut crate::leanh::LeanObject,
    mut v_k_8135_: *mut crate::leanh::LeanObject,
    mut v_a_8136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8137_ = crate::leanh::lean_box(0);
    v___x_8138_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8134_,
        v_k_8135_,
        v___x_8137_,
        v_a_8136_,
    );
    return v___x_8138_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(
    mut v_00_u03b1_8139_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8140_: *mut crate::leanh::LeanObject,
    mut v_inst_8141_: *mut crate::leanh::LeanObject,
    mut v_k_8142_: *mut crate::leanh::LeanObject,
    mut v_a_8143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8144_ = crate::leanh::lean_box(0);
    v___x_8145_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8141_,
        v_k_8142_,
        v___x_8144_,
        v_a_8143_,
    );
    return v___x_8145_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
    mut v_inst_8146_: *mut crate::leanh::LeanObject,
    mut v_k_8147_: *mut crate::leanh::LeanObject,
    mut v_best_8148_: *mut crate::leanh::LeanObject,
    mut v_a_8149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8155_: u8 = 0;
    let mut v___x_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_8149_) == 0 {
                    v_k_8150_ = crate::leanh::lean_ctor_get(v_a_8149_, 1);
                    crate::leanh::lean_inc_n(v_k_8150_, 2);
                    v_v_8151_ = crate::leanh::lean_ctor_get(v_a_8149_, 2);
                    crate::leanh::lean_inc(v_v_8151_);
                    v_l_8152_ = crate::leanh::lean_ctor_get(v_a_8149_, 3);
                    crate::leanh::lean_inc(v_l_8152_);
                    v_r_8153_ = crate::leanh::lean_ctor_get(v_a_8149_, 4);
                    crate::leanh::lean_inc(v_r_8153_);
                    crate::leanh::lean_dec_ref_known(v_a_8149_, 5);
                    crate::leanh::lean_inc_ref(v_inst_8146_);
                    crate::leanh::lean_inc(v_k_8147_);
                    v___x_8154_ = crate::leanh::lean_apply_2(v_inst_8146_, v_k_8147_, v_k_8150_);
                    v___x_8155_ = (crate::leanh::lean_unbox(v___x_8154_) as u8);
                    if v___x_8155_ == 0 {
                        crate::leanh::lean_dec(v_r_8153_);
                        crate::leanh::lean_dec(v_best_8148_);
                        v___x_8156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8156_, 0, v_k_8150_);
                        crate::leanh::lean_ctor_set(v___x_8156_, 1, v_v_8151_);
                        v___x_8157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8157_, 0, v___x_8156_);
                        v_best_8148_ = v___x_8157_;
                        v_a_8149_ = v_l_8152_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_8152_);
                        crate::leanh::lean_dec(v_v_8151_);
                        crate::leanh::lean_dec(v_k_8150_);
                        v_a_8149_ = v_r_8153_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8147_);
                    crate::leanh::lean_dec_ref(v_inst_8146_);
                    return v_best_8148_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(
    mut v_00_u03b1_8160_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8161_: *mut crate::leanh::LeanObject,
    mut v_inst_8162_: *mut crate::leanh::LeanObject,
    mut v_k_8163_: *mut crate::leanh::LeanObject,
    mut v_best_8164_: *mut crate::leanh::LeanObject,
    mut v_a_8165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8166_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8162_,
        v_k_8163_,
        v_best_8164_,
        v_a_8165_,
    );
    return v___x_8166_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(
    mut v_inst_8167_: *mut crate::leanh::LeanObject,
    mut v_k_8168_: *mut crate::leanh::LeanObject,
    mut v_a_8169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8170_ = crate::leanh::lean_box(0);
    v___x_8171_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8167_,
        v_k_8168_,
        v___x_8170_,
        v_a_8169_,
    );
    return v___x_8171_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(
    mut v_00_u03b1_8172_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8173_: *mut crate::leanh::LeanObject,
    mut v_inst_8174_: *mut crate::leanh::LeanObject,
    mut v_k_8175_: *mut crate::leanh::LeanObject,
    mut v_a_8176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8177_ = crate::leanh::lean_box(0);
    v___x_8178_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8174_,
        v_k_8175_,
        v___x_8177_,
        v_a_8176_,
    );
    return v___x_8178_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
    mut v_inst_8179_: *mut crate::leanh::LeanObject,
    mut v_k_8180_: *mut crate::leanh::LeanObject,
    mut v_best_8181_: *mut crate::leanh::LeanObject,
    mut v_a_8182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8188_: u8 = 0;
    let mut v___x_8190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_8182_) == 0 {
                    v_k_8183_ = crate::leanh::lean_ctor_get(v_a_8182_, 1);
                    crate::leanh::lean_inc_n(v_k_8183_, 2);
                    v_v_8184_ = crate::leanh::lean_ctor_get(v_a_8182_, 2);
                    crate::leanh::lean_inc(v_v_8184_);
                    v_l_8185_ = crate::leanh::lean_ctor_get(v_a_8182_, 3);
                    crate::leanh::lean_inc(v_l_8185_);
                    v_r_8186_ = crate::leanh::lean_ctor_get(v_a_8182_, 4);
                    crate::leanh::lean_inc(v_r_8186_);
                    crate::leanh::lean_dec_ref_known(v_a_8182_, 5);
                    crate::leanh::lean_inc_ref(v_inst_8179_);
                    crate::leanh::lean_inc(v_k_8180_);
                    v___x_8187_ = crate::leanh::lean_apply_2(v_inst_8179_, v_k_8180_, v_k_8183_);
                    v___x_8188_ = (crate::leanh::lean_unbox(v___x_8187_) as u8);
                    match v___x_8188_ {
                        0 => {
                            crate::leanh::lean_dec(v_r_8186_);
                            crate::leanh::lean_dec(v_v_8184_);
                            crate::leanh::lean_dec(v_k_8183_);
                            v_a_8182_ = v_l_8185_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_r_8186_);
                            crate::leanh::lean_dec(v_l_8185_);
                            crate::leanh::lean_dec(v_best_8181_);
                            crate::leanh::lean_dec(v_k_8180_);
                            crate::leanh::lean_dec_ref(v_inst_8179_);
                            v___x_8190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8190_, 0, v_k_8183_);
                            crate::leanh::lean_ctor_set(v___x_8190_, 1, v_v_8184_);
                            v___x_8191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8191_, 0, v___x_8190_);
                            return v___x_8191_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_8185_);
                            crate::leanh::lean_dec(v_best_8181_);
                            v___x_8192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8192_, 0, v_k_8183_);
                            crate::leanh::lean_ctor_set(v___x_8192_, 1, v_v_8184_);
                            v___x_8193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8193_, 0, v___x_8192_);
                            v_best_8181_ = v___x_8193_;
                            v_a_8182_ = v_r_8186_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8180_);
                    crate::leanh::lean_dec_ref(v_inst_8179_);
                    return v_best_8181_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(
    mut v_00_u03b1_8195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8196_: *mut crate::leanh::LeanObject,
    mut v_inst_8197_: *mut crate::leanh::LeanObject,
    mut v_k_8198_: *mut crate::leanh::LeanObject,
    mut v_best_8199_: *mut crate::leanh::LeanObject,
    mut v_a_8200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8201_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8197_,
        v_k_8198_,
        v_best_8199_,
        v_a_8200_,
    );
    return v___x_8201_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(
    mut v_inst_8202_: *mut crate::leanh::LeanObject,
    mut v_k_8203_: *mut crate::leanh::LeanObject,
    mut v_a_8204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8205_ = crate::leanh::lean_box(0);
    v___x_8206_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8202_,
        v_k_8203_,
        v___x_8205_,
        v_a_8204_,
    );
    return v___x_8206_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(
    mut v_00_u03b1_8207_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8208_: *mut crate::leanh::LeanObject,
    mut v_inst_8209_: *mut crate::leanh::LeanObject,
    mut v_k_8210_: *mut crate::leanh::LeanObject,
    mut v_a_8211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8212_ = crate::leanh::lean_box(0);
    v___x_8213_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8209_,
        v_k_8210_,
        v___x_8212_,
        v_a_8211_,
    );
    return v___x_8213_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
    mut v_inst_8214_: *mut crate::leanh::LeanObject,
    mut v_k_8215_: *mut crate::leanh::LeanObject,
    mut v_best_8216_: *mut crate::leanh::LeanObject,
    mut v_a_8217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: u8 = 0;
    let mut v___x_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_8217_) == 0 {
                    v_k_8218_ = crate::leanh::lean_ctor_get(v_a_8217_, 1);
                    crate::leanh::lean_inc_n(v_k_8218_, 2);
                    v_v_8219_ = crate::leanh::lean_ctor_get(v_a_8217_, 2);
                    crate::leanh::lean_inc(v_v_8219_);
                    v_l_8220_ = crate::leanh::lean_ctor_get(v_a_8217_, 3);
                    crate::leanh::lean_inc(v_l_8220_);
                    v_r_8221_ = crate::leanh::lean_ctor_get(v_a_8217_, 4);
                    crate::leanh::lean_inc(v_r_8221_);
                    crate::leanh::lean_dec_ref_known(v_a_8217_, 5);
                    crate::leanh::lean_inc_ref(v_inst_8214_);
                    crate::leanh::lean_inc(v_k_8215_);
                    v___x_8222_ = crate::leanh::lean_apply_2(v_inst_8214_, v_k_8215_, v_k_8218_);
                    v___x_8223_ = (crate::leanh::lean_unbox(v___x_8222_) as u8);
                    if v___x_8223_ == 2 {
                        crate::leanh::lean_dec(v_l_8220_);
                        crate::leanh::lean_dec(v_best_8216_);
                        v___x_8224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8224_, 0, v_k_8218_);
                        crate::leanh::lean_ctor_set(v___x_8224_, 1, v_v_8219_);
                        v___x_8225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8225_, 0, v___x_8224_);
                        v_best_8216_ = v___x_8225_;
                        v_a_8217_ = v_r_8221_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_8221_);
                        crate::leanh::lean_dec(v_v_8219_);
                        crate::leanh::lean_dec(v_k_8218_);
                        v_a_8217_ = v_l_8220_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_8215_);
                    crate::leanh::lean_dec_ref(v_inst_8214_);
                    return v_best_8216_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(
    mut v_00_u03b1_8228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8229_: *mut crate::leanh::LeanObject,
    mut v_inst_8230_: *mut crate::leanh::LeanObject,
    mut v_k_8231_: *mut crate::leanh::LeanObject,
    mut v_best_8232_: *mut crate::leanh::LeanObject,
    mut v_a_8233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8234_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8230_,
        v_k_8231_,
        v_best_8232_,
        v_a_8233_,
    );
    return v___x_8234_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(
    mut v_inst_8235_: *mut crate::leanh::LeanObject,
    mut v_k_8236_: *mut crate::leanh::LeanObject,
    mut v_a_8237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8238_ = crate::leanh::lean_box(0);
    v___x_8239_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8235_,
        v_k_8236_,
        v___x_8238_,
        v_a_8237_,
    );
    return v___x_8239_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(
    mut v_00_u03b1_8240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8241_: *mut crate::leanh::LeanObject,
    mut v_inst_8242_: *mut crate::leanh::LeanObject,
    mut v_k_8243_: *mut crate::leanh::LeanObject,
    mut v_a_8244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8245_ = crate::leanh::lean_box(0);
    v___x_8246_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8242_,
        v_k_8243_,
        v___x_8245_,
        v_a_8244_,
    );
    return v___x_8246_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(
    mut v_inst_8247_: *mut crate::leanh::LeanObject,
    mut v_inst_8248_: *mut crate::leanh::LeanObject,
    mut v_k_8249_: *mut crate::leanh::LeanObject,
    mut v_t_8250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8251_ = crate::leanh::lean_box(0);
    v___x_8252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8247_,
        v_k_8249_,
        v___x_8251_,
        v_t_8250_,
    );
    if crate::leanh::lean_obj_tag(v___x_8252_) == 0 {
        let mut v___x_8253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8253_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8254_ = l_panic___redArg(v_inst_8248_, v___x_8253_);
        return v___x_8254_;
    } else {
        let mut v_val_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8255_ = crate::leanh::lean_ctor_get(v___x_8252_, 0);
        crate::leanh::lean_inc(v_val_8255_);
        crate::leanh::lean_dec_ref_known(v___x_8252_, 1);
        return v_val_8255_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(
    mut v_inst_8256_: *mut crate::leanh::LeanObject,
    mut v_inst_8257_: *mut crate::leanh::LeanObject,
    mut v_k_8258_: *mut crate::leanh::LeanObject,
    mut v_t_8259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8260_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(
        v_inst_8256_,
        v_inst_8257_,
        v_k_8258_,
        v_t_8259_,
    );
    crate::leanh::lean_dec_ref(v_inst_8257_);
    return v_res_8260_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(
    mut v_00_u03b1_8261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8262_: *mut crate::leanh::LeanObject,
    mut v_inst_8263_: *mut crate::leanh::LeanObject,
    mut v_inst_8264_: *mut crate::leanh::LeanObject,
    mut v_k_8265_: *mut crate::leanh::LeanObject,
    mut v_t_8266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8267_ = crate::leanh::lean_box(0);
    v___x_8268_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8263_,
        v_k_8265_,
        v___x_8267_,
        v_t_8266_,
    );
    if crate::leanh::lean_obj_tag(v___x_8268_) == 0 {
        let mut v___x_8269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8269_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8270_ = l_panic___redArg(v_inst_8264_, v___x_8269_);
        return v___x_8270_;
    } else {
        let mut v_val_8271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8271_ = crate::leanh::lean_ctor_get(v___x_8268_, 0);
        crate::leanh::lean_inc(v_val_8271_);
        crate::leanh::lean_dec_ref_known(v___x_8268_, 1);
        return v_val_8271_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(
    mut v_00_u03b1_8272_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8273_: *mut crate::leanh::LeanObject,
    mut v_inst_8274_: *mut crate::leanh::LeanObject,
    mut v_inst_8275_: *mut crate::leanh::LeanObject,
    mut v_k_8276_: *mut crate::leanh::LeanObject,
    mut v_t_8277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8278_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(
        v_00_u03b1_8272_,
        v_00_u03b2_8273_,
        v_inst_8274_,
        v_inst_8275_,
        v_k_8276_,
        v_t_8277_,
    );
    crate::leanh::lean_dec_ref(v_inst_8275_);
    return v_res_8278_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(
    mut v_inst_8279_: *mut crate::leanh::LeanObject,
    mut v_inst_8280_: *mut crate::leanh::LeanObject,
    mut v_k_8281_: *mut crate::leanh::LeanObject,
    mut v_t_8282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8283_ = crate::leanh::lean_box(0);
    v___x_8284_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8279_,
        v_k_8281_,
        v___x_8283_,
        v_t_8282_,
    );
    if crate::leanh::lean_obj_tag(v___x_8284_) == 0 {
        let mut v___x_8285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8285_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8286_ = l_panic___redArg(v_inst_8280_, v___x_8285_);
        return v___x_8286_;
    } else {
        let mut v_val_8287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8287_ = crate::leanh::lean_ctor_get(v___x_8284_, 0);
        crate::leanh::lean_inc(v_val_8287_);
        crate::leanh::lean_dec_ref_known(v___x_8284_, 1);
        return v_val_8287_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(
    mut v_inst_8288_: *mut crate::leanh::LeanObject,
    mut v_inst_8289_: *mut crate::leanh::LeanObject,
    mut v_k_8290_: *mut crate::leanh::LeanObject,
    mut v_t_8291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8292_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(
        v_inst_8288_,
        v_inst_8289_,
        v_k_8290_,
        v_t_8291_,
    );
    crate::leanh::lean_dec_ref(v_inst_8289_);
    return v_res_8292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(
    mut v_00_u03b1_8293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8294_: *mut crate::leanh::LeanObject,
    mut v_inst_8295_: *mut crate::leanh::LeanObject,
    mut v_inst_8296_: *mut crate::leanh::LeanObject,
    mut v_k_8297_: *mut crate::leanh::LeanObject,
    mut v_t_8298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8299_ = crate::leanh::lean_box(0);
    v___x_8300_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8295_,
        v_k_8297_,
        v___x_8299_,
        v_t_8298_,
    );
    if crate::leanh::lean_obj_tag(v___x_8300_) == 0 {
        let mut v___x_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8301_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8302_ = l_panic___redArg(v_inst_8296_, v___x_8301_);
        return v___x_8302_;
    } else {
        let mut v_val_8303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8303_ = crate::leanh::lean_ctor_get(v___x_8300_, 0);
        crate::leanh::lean_inc(v_val_8303_);
        crate::leanh::lean_dec_ref_known(v___x_8300_, 1);
        return v_val_8303_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(
    mut v_00_u03b1_8304_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8305_: *mut crate::leanh::LeanObject,
    mut v_inst_8306_: *mut crate::leanh::LeanObject,
    mut v_inst_8307_: *mut crate::leanh::LeanObject,
    mut v_k_8308_: *mut crate::leanh::LeanObject,
    mut v_t_8309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8310_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(
        v_00_u03b1_8304_,
        v_00_u03b2_8305_,
        v_inst_8306_,
        v_inst_8307_,
        v_k_8308_,
        v_t_8309_,
    );
    crate::leanh::lean_dec_ref(v_inst_8307_);
    return v_res_8310_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(
    mut v_inst_8311_: *mut crate::leanh::LeanObject,
    mut v_inst_8312_: *mut crate::leanh::LeanObject,
    mut v_k_8313_: *mut crate::leanh::LeanObject,
    mut v_t_8314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8315_ = crate::leanh::lean_box(0);
    v___x_8316_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8311_,
        v_k_8313_,
        v___x_8315_,
        v_t_8314_,
    );
    if crate::leanh::lean_obj_tag(v___x_8316_) == 0 {
        let mut v___x_8317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8317_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8318_ = l_panic___redArg(v_inst_8312_, v___x_8317_);
        return v___x_8318_;
    } else {
        let mut v_val_8319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8319_ = crate::leanh::lean_ctor_get(v___x_8316_, 0);
        crate::leanh::lean_inc(v_val_8319_);
        crate::leanh::lean_dec_ref_known(v___x_8316_, 1);
        return v_val_8319_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(
    mut v_inst_8320_: *mut crate::leanh::LeanObject,
    mut v_inst_8321_: *mut crate::leanh::LeanObject,
    mut v_k_8322_: *mut crate::leanh::LeanObject,
    mut v_t_8323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8324_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(
        v_inst_8320_,
        v_inst_8321_,
        v_k_8322_,
        v_t_8323_,
    );
    crate::leanh::lean_dec_ref(v_inst_8321_);
    return v_res_8324_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(
    mut v_00_u03b1_8325_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8326_: *mut crate::leanh::LeanObject,
    mut v_inst_8327_: *mut crate::leanh::LeanObject,
    mut v_inst_8328_: *mut crate::leanh::LeanObject,
    mut v_k_8329_: *mut crate::leanh::LeanObject,
    mut v_t_8330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8331_ = crate::leanh::lean_box(0);
    v___x_8332_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8327_,
        v_k_8329_,
        v___x_8331_,
        v_t_8330_,
    );
    if crate::leanh::lean_obj_tag(v___x_8332_) == 0 {
        let mut v___x_8333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8333_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8334_ = l_panic___redArg(v_inst_8328_, v___x_8333_);
        return v___x_8334_;
    } else {
        let mut v_val_8335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8335_ = crate::leanh::lean_ctor_get(v___x_8332_, 0);
        crate::leanh::lean_inc(v_val_8335_);
        crate::leanh::lean_dec_ref_known(v___x_8332_, 1);
        return v_val_8335_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(
    mut v_00_u03b1_8336_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8337_: *mut crate::leanh::LeanObject,
    mut v_inst_8338_: *mut crate::leanh::LeanObject,
    mut v_inst_8339_: *mut crate::leanh::LeanObject,
    mut v_k_8340_: *mut crate::leanh::LeanObject,
    mut v_t_8341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8342_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(
        v_00_u03b1_8336_,
        v_00_u03b2_8337_,
        v_inst_8338_,
        v_inst_8339_,
        v_k_8340_,
        v_t_8341_,
    );
    crate::leanh::lean_dec_ref(v_inst_8339_);
    return v_res_8342_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(
    mut v_inst_8343_: *mut crate::leanh::LeanObject,
    mut v_inst_8344_: *mut crate::leanh::LeanObject,
    mut v_k_8345_: *mut crate::leanh::LeanObject,
    mut v_t_8346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8347_ = crate::leanh::lean_box(0);
    v___x_8348_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8343_,
        v_k_8345_,
        v___x_8347_,
        v_t_8346_,
    );
    if crate::leanh::lean_obj_tag(v___x_8348_) == 0 {
        let mut v___x_8349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8349_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8350_ = l_panic___redArg(v_inst_8344_, v___x_8349_);
        return v___x_8350_;
    } else {
        let mut v_val_8351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8351_ = crate::leanh::lean_ctor_get(v___x_8348_, 0);
        crate::leanh::lean_inc(v_val_8351_);
        crate::leanh::lean_dec_ref_known(v___x_8348_, 1);
        return v_val_8351_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(
    mut v_inst_8352_: *mut crate::leanh::LeanObject,
    mut v_inst_8353_: *mut crate::leanh::LeanObject,
    mut v_k_8354_: *mut crate::leanh::LeanObject,
    mut v_t_8355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8356_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(
        v_inst_8352_,
        v_inst_8353_,
        v_k_8354_,
        v_t_8355_,
    );
    crate::leanh::lean_dec_ref(v_inst_8353_);
    return v_res_8356_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(
    mut v_00_u03b1_8357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8358_: *mut crate::leanh::LeanObject,
    mut v_inst_8359_: *mut crate::leanh::LeanObject,
    mut v_inst_8360_: *mut crate::leanh::LeanObject,
    mut v_k_8361_: *mut crate::leanh::LeanObject,
    mut v_t_8362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8363_ = crate::leanh::lean_box(0);
    v___x_8364_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8359_,
        v_k_8361_,
        v___x_8363_,
        v_t_8362_,
    );
    if crate::leanh::lean_obj_tag(v___x_8364_) == 0 {
        let mut v___x_8365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8365_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once
            ),
            _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3,
        );
        v___x_8366_ = l_panic___redArg(v_inst_8360_, v___x_8365_);
        return v___x_8366_;
    } else {
        let mut v_val_8367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8367_ = crate::leanh::lean_ctor_get(v___x_8364_, 0);
        crate::leanh::lean_inc(v_val_8367_);
        crate::leanh::lean_dec_ref_known(v___x_8364_, 1);
        return v_val_8367_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(
    mut v_00_u03b1_8368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8369_: *mut crate::leanh::LeanObject,
    mut v_inst_8370_: *mut crate::leanh::LeanObject,
    mut v_inst_8371_: *mut crate::leanh::LeanObject,
    mut v_k_8372_: *mut crate::leanh::LeanObject,
    mut v_t_8373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8374_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(
        v_00_u03b1_8368_,
        v_00_u03b2_8369_,
        v_inst_8370_,
        v_inst_8371_,
        v_k_8372_,
        v_t_8373_,
    );
    crate::leanh::lean_dec_ref(v_inst_8371_);
    return v_res_8374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(
    mut v_inst_8375_: *mut crate::leanh::LeanObject,
    mut v_k_8376_: *mut crate::leanh::LeanObject,
    mut v_t_8377_: *mut crate::leanh::LeanObject,
    mut v_fallback_8378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8379_ = crate::leanh::lean_box(0);
    v___x_8380_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8375_,
        v_k_8376_,
        v___x_8379_,
        v_t_8377_,
    );
    if crate::leanh::lean_obj_tag(v___x_8380_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8378_);
        return v_fallback_8378_;
    } else {
        let mut v_val_8381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8381_ = crate::leanh::lean_ctor_get(v___x_8380_, 0);
        crate::leanh::lean_inc(v_val_8381_);
        crate::leanh::lean_dec_ref_known(v___x_8380_, 1);
        return v_val_8381_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(
    mut v_inst_8382_: *mut crate::leanh::LeanObject,
    mut v_k_8383_: *mut crate::leanh::LeanObject,
    mut v_t_8384_: *mut crate::leanh::LeanObject,
    mut v_fallback_8385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8386_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(
        v_inst_8382_,
        v_k_8383_,
        v_t_8384_,
        v_fallback_8385_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8385_);
    return v_res_8386_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(
    mut v_00_u03b1_8387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8388_: *mut crate::leanh::LeanObject,
    mut v_inst_8389_: *mut crate::leanh::LeanObject,
    mut v_k_8390_: *mut crate::leanh::LeanObject,
    mut v_t_8391_: *mut crate::leanh::LeanObject,
    mut v_fallback_8392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8393_ = crate::leanh::lean_box(0);
    v___x_8394_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
        v_inst_8389_,
        v_k_8390_,
        v___x_8393_,
        v_t_8391_,
    );
    if crate::leanh::lean_obj_tag(v___x_8394_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8392_);
        return v_fallback_8392_;
    } else {
        let mut v_val_8395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8395_ = crate::leanh::lean_ctor_get(v___x_8394_, 0);
        crate::leanh::lean_inc(v_val_8395_);
        crate::leanh::lean_dec_ref_known(v___x_8394_, 1);
        return v_val_8395_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(
    mut v_00_u03b1_8396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8397_: *mut crate::leanh::LeanObject,
    mut v_inst_8398_: *mut crate::leanh::LeanObject,
    mut v_k_8399_: *mut crate::leanh::LeanObject,
    mut v_t_8400_: *mut crate::leanh::LeanObject,
    mut v_fallback_8401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8402_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(
        v_00_u03b1_8396_,
        v_00_u03b2_8397_,
        v_inst_8398_,
        v_k_8399_,
        v_t_8400_,
        v_fallback_8401_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8401_);
    return v_res_8402_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(
    mut v_inst_8403_: *mut crate::leanh::LeanObject,
    mut v_k_8404_: *mut crate::leanh::LeanObject,
    mut v_t_8405_: *mut crate::leanh::LeanObject,
    mut v_fallback_8406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8407_ = crate::leanh::lean_box(0);
    v___x_8408_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8403_,
        v_k_8404_,
        v___x_8407_,
        v_t_8405_,
    );
    if crate::leanh::lean_obj_tag(v___x_8408_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8406_);
        return v_fallback_8406_;
    } else {
        let mut v_val_8409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8409_ = crate::leanh::lean_ctor_get(v___x_8408_, 0);
        crate::leanh::lean_inc(v_val_8409_);
        crate::leanh::lean_dec_ref_known(v___x_8408_, 1);
        return v_val_8409_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(
    mut v_inst_8410_: *mut crate::leanh::LeanObject,
    mut v_k_8411_: *mut crate::leanh::LeanObject,
    mut v_t_8412_: *mut crate::leanh::LeanObject,
    mut v_fallback_8413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8414_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(
        v_inst_8410_,
        v_k_8411_,
        v_t_8412_,
        v_fallback_8413_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8413_);
    return v_res_8414_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(
    mut v_00_u03b1_8415_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8416_: *mut crate::leanh::LeanObject,
    mut v_inst_8417_: *mut crate::leanh::LeanObject,
    mut v_k_8418_: *mut crate::leanh::LeanObject,
    mut v_t_8419_: *mut crate::leanh::LeanObject,
    mut v_fallback_8420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8421_ = crate::leanh::lean_box(0);
    v___x_8422_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
        v_inst_8417_,
        v_k_8418_,
        v___x_8421_,
        v_t_8419_,
    );
    if crate::leanh::lean_obj_tag(v___x_8422_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8420_);
        return v_fallback_8420_;
    } else {
        let mut v_val_8423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8423_ = crate::leanh::lean_ctor_get(v___x_8422_, 0);
        crate::leanh::lean_inc(v_val_8423_);
        crate::leanh::lean_dec_ref_known(v___x_8422_, 1);
        return v_val_8423_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(
    mut v_00_u03b1_8424_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8425_: *mut crate::leanh::LeanObject,
    mut v_inst_8426_: *mut crate::leanh::LeanObject,
    mut v_k_8427_: *mut crate::leanh::LeanObject,
    mut v_t_8428_: *mut crate::leanh::LeanObject,
    mut v_fallback_8429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8430_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(
        v_00_u03b1_8424_,
        v_00_u03b2_8425_,
        v_inst_8426_,
        v_k_8427_,
        v_t_8428_,
        v_fallback_8429_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8429_);
    return v_res_8430_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(
    mut v_inst_8431_: *mut crate::leanh::LeanObject,
    mut v_k_8432_: *mut crate::leanh::LeanObject,
    mut v_t_8433_: *mut crate::leanh::LeanObject,
    mut v_fallback_8434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8435_ = crate::leanh::lean_box(0);
    v___x_8436_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8431_,
        v_k_8432_,
        v___x_8435_,
        v_t_8433_,
    );
    if crate::leanh::lean_obj_tag(v___x_8436_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8434_);
        return v_fallback_8434_;
    } else {
        let mut v_val_8437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8437_ = crate::leanh::lean_ctor_get(v___x_8436_, 0);
        crate::leanh::lean_inc(v_val_8437_);
        crate::leanh::lean_dec_ref_known(v___x_8436_, 1);
        return v_val_8437_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(
    mut v_inst_8438_: *mut crate::leanh::LeanObject,
    mut v_k_8439_: *mut crate::leanh::LeanObject,
    mut v_t_8440_: *mut crate::leanh::LeanObject,
    mut v_fallback_8441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8442_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(
        v_inst_8438_,
        v_k_8439_,
        v_t_8440_,
        v_fallback_8441_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8441_);
    return v_res_8442_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(
    mut v_00_u03b1_8443_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8444_: *mut crate::leanh::LeanObject,
    mut v_inst_8445_: *mut crate::leanh::LeanObject,
    mut v_k_8446_: *mut crate::leanh::LeanObject,
    mut v_t_8447_: *mut crate::leanh::LeanObject,
    mut v_fallback_8448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8449_ = crate::leanh::lean_box(0);
    v___x_8450_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
        v_inst_8445_,
        v_k_8446_,
        v___x_8449_,
        v_t_8447_,
    );
    if crate::leanh::lean_obj_tag(v___x_8450_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8448_);
        return v_fallback_8448_;
    } else {
        let mut v_val_8451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8451_ = crate::leanh::lean_ctor_get(v___x_8450_, 0);
        crate::leanh::lean_inc(v_val_8451_);
        crate::leanh::lean_dec_ref_known(v___x_8450_, 1);
        return v_val_8451_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(
    mut v_00_u03b1_8452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8453_: *mut crate::leanh::LeanObject,
    mut v_inst_8454_: *mut crate::leanh::LeanObject,
    mut v_k_8455_: *mut crate::leanh::LeanObject,
    mut v_t_8456_: *mut crate::leanh::LeanObject,
    mut v_fallback_8457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8458_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(
        v_00_u03b1_8452_,
        v_00_u03b2_8453_,
        v_inst_8454_,
        v_k_8455_,
        v_t_8456_,
        v_fallback_8457_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8457_);
    return v_res_8458_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(
    mut v_inst_8459_: *mut crate::leanh::LeanObject,
    mut v_k_8460_: *mut crate::leanh::LeanObject,
    mut v_t_8461_: *mut crate::leanh::LeanObject,
    mut v_fallback_8462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8463_ = crate::leanh::lean_box(0);
    v___x_8464_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8459_,
        v_k_8460_,
        v___x_8463_,
        v_t_8461_,
    );
    if crate::leanh::lean_obj_tag(v___x_8464_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8462_);
        return v_fallback_8462_;
    } else {
        let mut v_val_8465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8465_ = crate::leanh::lean_ctor_get(v___x_8464_, 0);
        crate::leanh::lean_inc(v_val_8465_);
        crate::leanh::lean_dec_ref_known(v___x_8464_, 1);
        return v_val_8465_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(
    mut v_inst_8466_: *mut crate::leanh::LeanObject,
    mut v_k_8467_: *mut crate::leanh::LeanObject,
    mut v_t_8468_: *mut crate::leanh::LeanObject,
    mut v_fallback_8469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8470_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(
        v_inst_8466_,
        v_k_8467_,
        v_t_8468_,
        v_fallback_8469_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8469_);
    return v_res_8470_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(
    mut v_00_u03b1_8471_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8472_: *mut crate::leanh::LeanObject,
    mut v_inst_8473_: *mut crate::leanh::LeanObject,
    mut v_k_8474_: *mut crate::leanh::LeanObject,
    mut v_t_8475_: *mut crate::leanh::LeanObject,
    mut v_fallback_8476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8477_ = crate::leanh::lean_box(0);
    v___x_8478_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
        v_inst_8473_,
        v_k_8474_,
        v___x_8477_,
        v_t_8475_,
    );
    if crate::leanh::lean_obj_tag(v___x_8478_) == 0 {
        crate::leanh::lean_inc_ref(v_fallback_8476_);
        return v_fallback_8476_;
    } else {
        let mut v_val_8479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_8479_ = crate::leanh::lean_ctor_get(v___x_8478_, 0);
        crate::leanh::lean_inc(v_val_8479_);
        crate::leanh::lean_dec_ref_known(v___x_8478_, 1);
        return v_val_8479_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(
    mut v_00_u03b1_8480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8481_: *mut crate::leanh::LeanObject,
    mut v_inst_8482_: *mut crate::leanh::LeanObject,
    mut v_k_8483_: *mut crate::leanh::LeanObject,
    mut v_t_8484_: *mut crate::leanh::LeanObject,
    mut v_fallback_8485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8486_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(
        v_00_u03b1_8480_,
        v_00_u03b2_8481_,
        v_inst_8482_,
        v_k_8483_,
        v_t_8484_,
        v_fallback_8485_,
    );
    crate::leanh::lean_dec_ref(v_fallback_8485_);
    return v_res_8486_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(
    mut v_inst_8487_: *mut crate::leanh::LeanObject,
    mut v_k_8488_: *mut crate::leanh::LeanObject,
    mut v_x_8489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: u8 = 0;
    let mut v___x_8496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_8490_ = crate::leanh::lean_ctor_get(v_x_8489_, 1);
                crate::leanh::lean_inc_n(v_k_8490_, 2);
                v_v_8491_ = crate::leanh::lean_ctor_get(v_x_8489_, 2);
                crate::leanh::lean_inc(v_v_8491_);
                v_l_8492_ = crate::leanh::lean_ctor_get(v_x_8489_, 3);
                crate::leanh::lean_inc(v_l_8492_);
                v_r_8493_ = crate::leanh::lean_ctor_get(v_x_8489_, 4);
                crate::leanh::lean_inc(v_r_8493_);
                crate::leanh::lean_dec(v_x_8489_);
                crate::leanh::lean_inc_ref(v_inst_8487_);
                crate::leanh::lean_inc(v_k_8488_);
                v___x_8494_ = crate::leanh::lean_apply_2(v_inst_8487_, v_k_8488_, v_k_8490_);
                v___x_8495_ = (crate::leanh::lean_unbox(v___x_8494_) as u8);
                match v___x_8495_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_8493_);
                        v___x_8496_ = crate::leanh::lean_box(0);
                        v___x_8497_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(
                            v_inst_8487_,
                            v_k_8488_,
                            v___x_8496_,
                            v_l_8492_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8497_) == 0 {
                            v___x_8498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8498_, 0, v_k_8490_);
                            crate::leanh::lean_ctor_set(v___x_8498_, 1, v_v_8491_);
                            return v___x_8498_;
                        } else {
                            crate::leanh::lean_dec(v_v_8491_);
                            crate::leanh::lean_dec(v_k_8490_);
                            v_val_8499_ = crate::leanh::lean_ctor_get(v___x_8497_, 0);
                            crate::leanh::lean_inc(v_val_8499_);
                            crate::leanh::lean_dec_ref_known(v___x_8497_, 1);
                            return v_val_8499_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_8493_);
                        crate::leanh::lean_dec(v_l_8492_);
                        crate::leanh::lean_dec(v_k_8488_);
                        crate::leanh::lean_dec_ref(v_inst_8487_);
                        v___x_8500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8500_, 0, v_k_8490_);
                        crate::leanh::lean_ctor_set(v___x_8500_, 1, v_v_8491_);
                        return v___x_8500_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_8492_);
                        crate::leanh::lean_dec(v_v_8491_);
                        crate::leanh::lean_dec(v_k_8490_);
                        v_x_8489_ = v_r_8493_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(
    mut v_00_u03b1_8502_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8503_: *mut crate::leanh::LeanObject,
    mut v_inst_8504_: *mut crate::leanh::LeanObject,
    mut v_inst_8505_: *mut crate::leanh::LeanObject,
    mut v_k_8506_: *mut crate::leanh::LeanObject,
    mut v_x_8507_: *mut crate::leanh::LeanObject,
    mut v_x_8508_: *mut crate::leanh::LeanObject,
    mut v_x_8509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8510_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_8504_, v_k_8506_, v_x_8507_);
    return v___x_8510_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(
    mut v_inst_8511_: *mut crate::leanh::LeanObject,
    mut v_k_8512_: *mut crate::leanh::LeanObject,
    mut v_x_8513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8519_: u8 = 0;
    let mut v___x_8520_: u8 = 0;
    let mut v___x_8521_: u8 = 0;
    let mut v___x_8523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_8514_ = crate::leanh::lean_ctor_get(v_x_8513_, 1);
                crate::leanh::lean_inc_n(v_k_8514_, 2);
                v_v_8515_ = crate::leanh::lean_ctor_get(v_x_8513_, 2);
                crate::leanh::lean_inc(v_v_8515_);
                v_l_8516_ = crate::leanh::lean_ctor_get(v_x_8513_, 3);
                crate::leanh::lean_inc(v_l_8516_);
                v_r_8517_ = crate::leanh::lean_ctor_get(v_x_8513_, 4);
                crate::leanh::lean_inc(v_r_8517_);
                crate::leanh::lean_dec(v_x_8513_);
                crate::leanh::lean_inc_ref(v_inst_8511_);
                crate::leanh::lean_inc(v_k_8512_);
                v___x_8518_ = crate::leanh::lean_apply_2(v_inst_8511_, v_k_8512_, v_k_8514_);
                v___x_8519_ = 0;
                v___x_8520_ = (crate::leanh::lean_unbox(v___x_8518_) as u8);
                v___x_8521_ = l_instDecidableEqOrdering(v___x_8520_, v___x_8519_);
                if v___x_8521_ == 0 {
                    crate::leanh::lean_dec(v_l_8516_);
                    crate::leanh::lean_dec(v_v_8515_);
                    crate::leanh::lean_dec(v_k_8514_);
                    v_x_8513_ = v_r_8517_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_8517_);
                    v___x_8523_ = crate::leanh::lean_box(0);
                    v___x_8524_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(
                        v_inst_8511_,
                        v_k_8512_,
                        v___x_8523_,
                        v_l_8516_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8524_) == 0 {
                        v___x_8525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8525_, 0, v_k_8514_);
                        crate::leanh::lean_ctor_set(v___x_8525_, 1, v_v_8515_);
                        return v___x_8525_;
                    } else {
                        crate::leanh::lean_dec(v_v_8515_);
                        crate::leanh::lean_dec(v_k_8514_);
                        v_val_8526_ = crate::leanh::lean_ctor_get(v___x_8524_, 0);
                        crate::leanh::lean_inc(v_val_8526_);
                        crate::leanh::lean_dec_ref_known(v___x_8524_, 1);
                        return v_val_8526_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(
    mut v_00_u03b1_8527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8528_: *mut crate::leanh::LeanObject,
    mut v_inst_8529_: *mut crate::leanh::LeanObject,
    mut v_inst_8530_: *mut crate::leanh::LeanObject,
    mut v_k_8531_: *mut crate::leanh::LeanObject,
    mut v_x_8532_: *mut crate::leanh::LeanObject,
    mut v_x_8533_: *mut crate::leanh::LeanObject,
    mut v_x_8534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8535_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_8529_, v_k_8531_, v_x_8532_);
    return v___x_8535_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(
    mut v_inst_8536_: *mut crate::leanh::LeanObject,
    mut v_k_8537_: *mut crate::leanh::LeanObject,
    mut v_x_8538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8544_: u8 = 0;
    let mut v___x_8546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_8539_ = crate::leanh::lean_ctor_get(v_x_8538_, 1);
                crate::leanh::lean_inc_n(v_k_8539_, 2);
                v_v_8540_ = crate::leanh::lean_ctor_get(v_x_8538_, 2);
                crate::leanh::lean_inc(v_v_8540_);
                v_l_8541_ = crate::leanh::lean_ctor_get(v_x_8538_, 3);
                crate::leanh::lean_inc(v_l_8541_);
                v_r_8542_ = crate::leanh::lean_ctor_get(v_x_8538_, 4);
                crate::leanh::lean_inc(v_r_8542_);
                crate::leanh::lean_dec(v_x_8538_);
                crate::leanh::lean_inc_ref(v_inst_8536_);
                crate::leanh::lean_inc(v_k_8537_);
                v___x_8543_ = crate::leanh::lean_apply_2(v_inst_8536_, v_k_8537_, v_k_8539_);
                v___x_8544_ = (crate::leanh::lean_unbox(v___x_8543_) as u8);
                match v___x_8544_ {
                    0 => {
                        crate::leanh::lean_dec(v_r_8542_);
                        crate::leanh::lean_dec(v_v_8540_);
                        crate::leanh::lean_dec(v_k_8539_);
                        v_x_8538_ = v_l_8541_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_r_8542_);
                        crate::leanh::lean_dec(v_l_8541_);
                        crate::leanh::lean_dec(v_k_8537_);
                        crate::leanh::lean_dec_ref(v_inst_8536_);
                        v___x_8546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8546_, 0, v_k_8539_);
                        crate::leanh::lean_ctor_set(v___x_8546_, 1, v_v_8540_);
                        return v___x_8546_;
                    }
                    _ => {
                        crate::leanh::lean_dec(v_l_8541_);
                        v___x_8547_ = crate::leanh::lean_box(0);
                        v___x_8548_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(
                            v_inst_8536_,
                            v_k_8537_,
                            v___x_8547_,
                            v_r_8542_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8548_) == 0 {
                            v___x_8549_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8549_, 0, v_k_8539_);
                            crate::leanh::lean_ctor_set(v___x_8549_, 1, v_v_8540_);
                            return v___x_8549_;
                        } else {
                            crate::leanh::lean_dec(v_v_8540_);
                            crate::leanh::lean_dec(v_k_8539_);
                            v_val_8550_ = crate::leanh::lean_ctor_get(v___x_8548_, 0);
                            crate::leanh::lean_inc(v_val_8550_);
                            crate::leanh::lean_dec_ref_known(v___x_8548_, 1);
                            return v_val_8550_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(
    mut v_00_u03b1_8551_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8552_: *mut crate::leanh::LeanObject,
    mut v_inst_8553_: *mut crate::leanh::LeanObject,
    mut v_inst_8554_: *mut crate::leanh::LeanObject,
    mut v_k_8555_: *mut crate::leanh::LeanObject,
    mut v_x_8556_: *mut crate::leanh::LeanObject,
    mut v_x_8557_: *mut crate::leanh::LeanObject,
    mut v_x_8558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8559_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_8553_, v_k_8555_, v_x_8556_);
    return v___x_8559_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(
    mut v_inst_8560_: *mut crate::leanh::LeanObject,
    mut v_k_8561_: *mut crate::leanh::LeanObject,
    mut v_x_8562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_8563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_8565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_8566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: u8 = 0;
    let mut v___x_8569_: u8 = 0;
    let mut v___x_8570_: u8 = 0;
    let mut v___x_8572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_8563_ = crate::leanh::lean_ctor_get(v_x_8562_, 1);
                crate::leanh::lean_inc_n(v_k_8563_, 2);
                v_v_8564_ = crate::leanh::lean_ctor_get(v_x_8562_, 2);
                crate::leanh::lean_inc(v_v_8564_);
                v_l_8565_ = crate::leanh::lean_ctor_get(v_x_8562_, 3);
                crate::leanh::lean_inc(v_l_8565_);
                v_r_8566_ = crate::leanh::lean_ctor_get(v_x_8562_, 4);
                crate::leanh::lean_inc(v_r_8566_);
                crate::leanh::lean_dec(v_x_8562_);
                crate::leanh::lean_inc_ref(v_inst_8560_);
                crate::leanh::lean_inc(v_k_8561_);
                v___x_8567_ = crate::leanh::lean_apply_2(v_inst_8560_, v_k_8561_, v_k_8563_);
                v___x_8568_ = 2;
                v___x_8569_ = (crate::leanh::lean_unbox(v___x_8567_) as u8);
                v___x_8570_ = l_instDecidableEqOrdering(v___x_8569_, v___x_8568_);
                if v___x_8570_ == 0 {
                    crate::leanh::lean_dec(v_r_8566_);
                    crate::leanh::lean_dec(v_v_8564_);
                    crate::leanh::lean_dec(v_k_8563_);
                    v_x_8562_ = v_l_8565_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_8565_);
                    v___x_8572_ = crate::leanh::lean_box(0);
                    v___x_8573_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(
                        v_inst_8560_,
                        v_k_8561_,
                        v___x_8572_,
                        v_r_8566_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8573_) == 0 {
                        v___x_8574_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8574_, 0, v_k_8563_);
                        crate::leanh::lean_ctor_set(v___x_8574_, 1, v_v_8564_);
                        return v___x_8574_;
                    } else {
                        crate::leanh::lean_dec(v_v_8564_);
                        crate::leanh::lean_dec(v_k_8563_);
                        v_val_8575_ = crate::leanh::lean_ctor_get(v___x_8573_, 0);
                        crate::leanh::lean_inc(v_val_8575_);
                        crate::leanh::lean_dec_ref_known(v___x_8573_, 1);
                        return v_val_8575_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(
    mut v_00_u03b1_8576_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_8577_: *mut crate::leanh::LeanObject,
    mut v_inst_8578_: *mut crate::leanh::LeanObject,
    mut v_inst_8579_: *mut crate::leanh::LeanObject,
    mut v_k_8580_: *mut crate::leanh::LeanObject,
    mut v_x_8581_: *mut crate::leanh::LeanObject,
    mut v_x_8582_: *mut crate::leanh::LeanObject,
    mut v_x_8583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8584_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_8578_, v_k_8580_, v_x_8581_);
    return v___x_8584_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Queries(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Compare(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Ordered(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Queries(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Queries(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Compare(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Ordered(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
}
