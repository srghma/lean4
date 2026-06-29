// Lean compiler output
// Module: Init.Data.String.OrderInstances
// Imports: Init.Data.String.Defs Init.Grind.ToInt Init.Data.Order.Classes Init.Data.Order.PackageFactories Init.Omega Init.Data.Order.PackageFactories
use crate::r#gen::Init::Data::Int::Basic::l_Int_ofNat___boxed;
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::PackageFactories::{
    initialize_Init_Data_Order_PackageFactories,
    l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed,
    runtime_initialize_Init_Data_Order_PackageFactories,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, l_String_Slice_instDecidableEqPos___boxed,
    l_String_instDecidableEqPos___boxed, l_String_instDecidableLePos___boxed,
    l_String_instDecidableLePos__1___boxed, l_String_instDecidableLtPos___boxed,
    l_String_instDecidableLtPos__1___boxed, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::PosRaw::{
    l_String_instDecidableLeRaw___boxed, l_String_instDecidableLtRaw___boxed,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node6, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27, l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instDecidableEqRaw___boxed,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
};
pub static l_String_Internal_tacticOrder___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [83, 116, 114, 105, 110, 103, 0],
    };
static mut l_String_Internal_tacticOrder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal_tacticOrder___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
    };
static mut l_String_Internal_tacticOrder___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal_tacticOrder___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 97, 99, 116, 105, 99, 79, 114, 100, 101, 114, 0],
    };
static mut l_String_Internal_tacticOrder___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_String_Internal_tacticOrder___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3136308715950998022 as *mut crate::leanh::LeanObject,
        ],
    };
static l_String_Internal_tacticOrder___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__1_value)
                as *mut crate::leanh::LeanObject,
            14242566666915053831 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_String_Internal_tacticOrder___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__2_value)
                as *mut crate::leanh::LeanObject,
            935055145667255025 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_String_Internal_tacticOrder___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal_tacticOrder___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 114, 100, 101, 114, 0],
    };
static mut l_String_Internal_tacticOrder___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal_tacticOrder___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__4_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_String_Internal_tacticOrder___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal_tacticOrder___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_String_Internal_tacticOrder___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Internal_tacticOrder: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value) as *mut crate::leanh::LeanObject,10468396288943149198 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value) as *mut crate::leanh::LeanObject,12783917532758215986 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value) as *mut crate::leanh::LeanObject,7383208167966365478 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [80, 111, 115, 46, 82, 97, 119, 46, 108, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [80, 111, 115, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 97, 119, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,3418672936842095366 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,15887729272452159037 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject,15039634743260506134 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,7867407217964523712 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject,7139535056111981695 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [80, 111, 115, 46, 82, 97, 119, 46, 108, 101, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,3418672936842095366 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,15887729272452159037 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject,11634337043486632133 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,7867407217964523712 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject,16048779437067558268 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 116, 114, 105, 110, 103, 46, 80, 111, 115, 46, 108, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject,5184953075697731772 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 116, 114, 105, 110, 103, 46, 80, 111, 115, 46, 108, 101, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject,6464590044885214527 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 108, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 108, 105, 99, 101, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject,1627628403610607223 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value) as *mut crate::leanh::LeanObject,15868287955852075982 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 108, 101, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject,7735179832832806436 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value) as *mut crate::leanh::LeanObject,12054065949736598989 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [80, 111, 115, 46, 82, 97, 119, 46, 101, 120, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 120, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,3418672936842095366 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,15887729272452159037 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject,10370188395765544515 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value) as *mut crate::leanh::LeanObject,7867407217964523712 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject,7558250302867965522 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [83, 116, 114, 105, 110, 103, 46, 80, 111, 115, 46, 101, 120, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject,8673766875658292329 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 101, 120, 116, 95, 105, 102, 102, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68_value) as *mut crate::leanh::LeanObject;
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject,3358755654075404026 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal_tacticOrder___closed__0_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value) as *mut crate::leanh::LeanObject,16789909477982849867 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value) as *mut crate::leanh::LeanObject,1767494567867404924 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 116, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 87, 105, 108, 100, 99, 97, 114, 100, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value) as *mut crate::leanh::LeanObject,1262264483427375750 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value) as *mut crate::leanh::LeanObject,10962186005905108258 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 109, 101, 103, 97, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value) as *mut crate::leanh::LeanObject;
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value) as *mut crate::leanh::LeanObject,14893461734720614794 as *mut crate::leanh::LeanObject] };
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value) as *mut crate::leanh::LeanObject;
pub static l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91_value) as *mut crate::leanh::LeanObject;
pub static l_String_Pos_Raw_instToIntCiOfNatInt_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_String_Pos_Raw_instToIntCiOfNatInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instToIntCiOfNatInt_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Pos_Raw_instTransLe: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Pos_Raw_instLinearOrderPackage___closed__0_value:
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
    m_fun: l_String_Pos_Raw_instLinearOrderPackage___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Pos_Raw_instLinearOrderPackage___closed__1_value:
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
    m_fun: l_String_Pos_Raw_instLinearOrderPackage___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Pos_Raw_instLinearOrderPackage___closed__2_value:
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
    m_fun: l_String_instDecidableLeRaw___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Pos_Raw_instLinearOrderPackage___closed__4_value:
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
    m_fun: l_String_instDecidableLtRaw___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Pos_Raw_instLinearOrderPackage___closed__5_value:
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
    m_fun: l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Pos_Raw_instLinearOrderPackage___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Pos_Raw_instLinearOrderPackage___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_String_Pos_Raw_instLinearOrderPackage: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_504_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16;
    v___x_514_ = l_String_toRawSubstring_x27(v___x_513_);
    return v___x_514_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26;
    v___x_536_ = l_String_toRawSubstring_x27(v___x_535_);
    return v___x_536_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33;
    v___x_555_ = l_String_toRawSubstring_x27(v___x_554_);
    return v___x_555_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38;
    v___x_568_ = l_String_toRawSubstring_x27(v___x_567_);
    return v___x_568_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43;
    v___x_581_ = l_String_toRawSubstring_x27(v___x_580_);
    return v___x_581_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50;
    v___x_600_ = l_String_toRawSubstring_x27(v___x_599_);
    return v___x_600_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_617_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56;
    v___x_618_ = l_String_toRawSubstring_x27(v___x_617_);
    return v___x_618_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63;
    v___x_637_ = l_String_toRawSubstring_x27(v___x_636_);
    return v___x_637_;
}
pub unsafe fn _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69()
-> *mut crate::leanh::LeanObject {
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68;
    v___x_650_ = l_String_toRawSubstring_x27(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1(
    mut v_x_708_: *mut crate::leanh::LeanObject,
    mut v_a_709_: *mut crate::leanh::LeanObject,
    mut v_a_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    v___x_711_ = l_String_Internal_tacticOrder___closed__3;
    v___x_712_ = l_Lean_Syntax_isOfKind(v_x_708_, v___x_711_);
    if v___x_712_ == 0 {
        let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_713_ = crate::leanh::lean_box(1);
        v___x_714_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_714_, 0, v___x_713_);
        crate::leanh::lean_ctor_set(v___x_714_, 1, v_a_710_);
        return v___x_714_;
    } else {
        let mut v_quotContext_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: u8 = 0;
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_715_ = crate::leanh::lean_ctor_get(v_a_709_, 1);
        v_currMacroScope_716_ = crate::leanh::lean_ctor_get(v_a_709_, 2);
        v_ref_717_ = crate::leanh::lean_ctor_get(v_a_709_, 5);
        v___x_718_ = 0;
        v___x_719_ = l_Lean_SourceInfo_fromRef(v_ref_717_, v___x_718_);
        v___x_720_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4;
        v___x_721_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5;
        crate::leanh::lean_inc_n(v___x_719_, 43);
        v___x_722_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_722_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_722_, 1, v___x_721_);
        v___x_723_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7;
        v___x_724_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8;
        v___x_725_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9;
        v___x_726_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_726_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_726_, 1, v___x_724_);
        v___x_727_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11;
        v___x_728_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12);
        v___x_729_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_729_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_729_, 1, v___x_723_);
        crate::leanh::lean_ctor_set(v___x_729_, 2, v___x_728_);
        crate::leanh::lean_inc_ref_n(v___x_729_, 20);
        v___x_730_ = l_Lean_Syntax_node1(v___x_719_, v___x_727_, v___x_729_);
        v___x_731_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13;
        v___x_732_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_731_);
        v___x_733_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15;
        v___x_734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17);
        v___x_735_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21;
        crate::leanh::lean_inc_n(v_currMacroScope_716_, 9);
        crate::leanh::lean_inc_n(v_quotContext_715_, 9);
        v___x_736_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_735_, v_currMacroScope_716_);
        v___x_737_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24;
        v___x_738_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_738_, 1, v___x_734_);
        crate::leanh::lean_ctor_set(v___x_738_, 2, v___x_736_);
        crate::leanh::lean_ctor_set(v___x_738_, 3, v___x_737_);
        v___x_739_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_738_);
        v___x_740_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25;
        v___x_741_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_741_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_741_, 1, v___x_740_);
        v___x_742_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27);
        v___x_743_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29;
        v___x_744_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_743_, v_currMacroScope_716_);
        v___x_745_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32;
        v___x_746_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_746_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_746_, 1, v___x_742_);
        crate::leanh::lean_ctor_set(v___x_746_, 2, v___x_744_);
        crate::leanh::lean_ctor_set(v___x_746_, 3, v___x_745_);
        v___x_747_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_746_);
        v___x_748_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34);
        v___x_749_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35;
        v___x_750_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_749_, v_currMacroScope_716_);
        v___x_751_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37;
        v___x_752_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_752_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_752_, 1, v___x_748_);
        crate::leanh::lean_ctor_set(v___x_752_, 2, v___x_750_);
        crate::leanh::lean_ctor_set(v___x_752_, 3, v___x_751_);
        v___x_753_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_752_);
        v___x_754_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39);
        v___x_755_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40;
        v___x_756_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_755_, v_currMacroScope_716_);
        v___x_757_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42;
        v___x_758_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_758_, 1, v___x_754_);
        crate::leanh::lean_ctor_set(v___x_758_, 2, v___x_756_);
        crate::leanh::lean_ctor_set(v___x_758_, 3, v___x_757_);
        v___x_759_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_758_);
        v___x_760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44);
        v___x_761_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46;
        v___x_762_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_761_, v_currMacroScope_716_);
        v___x_763_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49;
        v___x_764_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_764_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_764_, 1, v___x_760_);
        crate::leanh::lean_ctor_set(v___x_764_, 2, v___x_762_);
        crate::leanh::lean_ctor_set(v___x_764_, 3, v___x_763_);
        v___x_765_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_764_);
        v___x_766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51);
        v___x_767_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52;
        v___x_768_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_767_, v_currMacroScope_716_);
        v___x_769_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55;
        v___x_770_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_770_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_766_);
        crate::leanh::lean_ctor_set(v___x_770_, 2, v___x_768_);
        crate::leanh::lean_ctor_set(v___x_770_, 3, v___x_769_);
        v___x_771_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_770_);
        v___x_772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57);
        v___x_773_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59;
        v___x_774_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_773_, v_currMacroScope_716_);
        v___x_775_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62;
        v___x_776_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_776_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_776_, 1, v___x_772_);
        crate::leanh::lean_ctor_set(v___x_776_, 2, v___x_774_);
        crate::leanh::lean_ctor_set(v___x_776_, 3, v___x_775_);
        v___x_777_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_776_);
        v___x_778_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64);
        v___x_779_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65;
        v___x_780_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_779_, v_currMacroScope_716_);
        v___x_781_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67;
        v___x_782_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_782_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_778_);
        crate::leanh::lean_ctor_set(v___x_782_, 2, v___x_780_);
        crate::leanh::lean_ctor_set(v___x_782_, 3, v___x_781_);
        v___x_783_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_782_);
        v___x_784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69), core::ptr::addr_of_mut!(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69_once), _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69);
        v___x_785_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70;
        v___x_786_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_785_, v_currMacroScope_716_);
        v___x_787_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73;
        v___x_788_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_784_);
        crate::leanh::lean_ctor_set(v___x_788_, 2, v___x_786_);
        crate::leanh::lean_ctor_set(v___x_788_, 3, v___x_787_);
        v___x_789_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_733_, v___x_729_, v___x_729_, v___x_788_);
        v___x_790_ = crate::leanh::lean_unsigned_to_nat(17);
        v___x_791_ = lean_mk_empty_array_with_capacity(v___x_790_);
        v___x_792_ = lean_array_push(v___x_791_, v___x_739_);
        crate::leanh::lean_inc_ref_n(v___x_741_, 7);
        v___x_793_ = lean_array_push(v___x_792_, v___x_741_);
        v___x_794_ = lean_array_push(v___x_793_, v___x_747_);
        v___x_795_ = lean_array_push(v___x_794_, v___x_741_);
        v___x_796_ = lean_array_push(v___x_795_, v___x_753_);
        v___x_797_ = lean_array_push(v___x_796_, v___x_741_);
        v___x_798_ = lean_array_push(v___x_797_, v___x_759_);
        v___x_799_ = lean_array_push(v___x_798_, v___x_741_);
        v___x_800_ = lean_array_push(v___x_799_, v___x_765_);
        v___x_801_ = lean_array_push(v___x_800_, v___x_741_);
        v___x_802_ = lean_array_push(v___x_801_, v___x_771_);
        v___x_803_ = lean_array_push(v___x_802_, v___x_741_);
        v___x_804_ = lean_array_push(v___x_803_, v___x_777_);
        v___x_805_ = lean_array_push(v___x_804_, v___x_741_);
        v___x_806_ = lean_array_push(v___x_805_, v___x_783_);
        v___x_807_ = lean_array_push(v___x_806_, v___x_741_);
        v___x_808_ = lean_array_push(v___x_807_, v___x_789_);
        v___x_809_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_809_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_809_, 1, v___x_723_);
        crate::leanh::lean_ctor_set(v___x_809_, 2, v___x_808_);
        v___x_810_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74;
        v___x_811_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_811_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_811_, 1, v___x_810_);
        v___x_812_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_723_, v___x_732_, v___x_809_, v___x_811_);
        v___x_813_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76;
        v___x_814_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77;
        v___x_815_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_814_);
        v___x_816_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79;
        v___x_817_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80;
        v___x_818_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_818_, 1, v___x_817_);
        v___x_819_ = l_Lean_Syntax_node1(v___x_719_, v___x_816_, v___x_818_);
        v___x_820_ = l_Lean_Syntax_node2(v___x_719_, v___x_813_, v___x_815_, v___x_819_);
        v___x_821_ = l_Lean_Syntax_node1(v___x_719_, v___x_723_, v___x_820_);
        crate::leanh::lean_inc(v___x_730_);
        v___x_822_ = l_Lean_Syntax_node6(
            v___x_719_, v___x_725_, v___x_726_, v___x_730_, v___x_729_, v___x_729_, v___x_812_,
            v___x_821_,
        );
        v___x_823_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81;
        v___x_824_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_824_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_824_, 1, v___x_823_);
        v___x_825_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83;
        v___x_826_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84;
        v___x_827_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_827_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_827_, 1, v___x_826_);
        v___x_828_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86;
        v___x_829_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88;
        v___x_830_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89;
        v___x_831_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90;
        v___x_832_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_832_, 1, v___x_830_);
        v___x_833_ = l_Lean_Syntax_node2(v___x_719_, v___x_831_, v___x_832_, v___x_730_);
        v___x_834_ = l_Lean_Syntax_node1(v___x_719_, v___x_723_, v___x_833_);
        v___x_835_ = l_Lean_Syntax_node1(v___x_719_, v___x_829_, v___x_834_);
        v___x_836_ = l_Lean_Syntax_node1(v___x_719_, v___x_828_, v___x_835_);
        v___x_837_ = l_Lean_Syntax_node2(v___x_719_, v___x_825_, v___x_827_, v___x_836_);
        v___x_838_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_723_, v___x_822_, v___x_824_, v___x_837_);
        v___x_839_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91;
        v___x_840_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_840_, 0, v___x_719_);
        crate::leanh::lean_ctor_set(v___x_840_, 1, v___x_839_);
        v___x_841_ =
            l_Lean_Syntax_node3(v___x_719_, v___x_720_, v___x_722_, v___x_838_, v___x_840_);
        v___x_842_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
        crate::leanh::lean_ctor_set(v___x_842_, 1, v_a_710_);
        return v___x_842_;
    }
}
pub unsafe fn l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___boxed(
    mut v_x_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_846_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1(v_x_843_, v_a_844_, v_a_845_);
    crate::leanh::lean_dec_ref(v_a_844_);
    return v_res_846_;
}
pub unsafe fn _init_l_String_Pos_Raw_instTransLe() -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = crate::leanh::lean_box(0);
    return v___x_848_;
}
pub unsafe fn l_String_Pos_Raw_instLinearOrderPackage___lam__0(
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_b_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_851_: u8 = 0;
    v___x_851_ = lean_nat_dec_le(v_a_849_, v_b_850_);
    if v___x_851_ == 0 {
        crate::leanh::lean_inc(v_b_850_);
        return v_b_850_;
    } else {
        crate::leanh::lean_inc(v_a_849_);
        return v_a_849_;
    }
}
pub unsafe fn l_String_Pos_Raw_instLinearOrderPackage___lam__0___boxed(
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_b_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_String_Pos_Raw_instLinearOrderPackage___lam__0(v_a_852_, v_b_853_);
    crate::leanh::lean_dec(v_b_853_);
    crate::leanh::lean_dec(v_a_852_);
    return v_res_854_;
}
pub unsafe fn l_String_Pos_Raw_instLinearOrderPackage___lam__1(
    mut v_a_855_: *mut crate::leanh::LeanObject,
    mut v_b_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: u8 = 0;
    v___x_857_ = lean_nat_dec_le(v_b_856_, v_a_855_);
    if v___x_857_ == 0 {
        crate::leanh::lean_inc(v_b_856_);
        return v_b_856_;
    } else {
        crate::leanh::lean_inc(v_a_855_);
        return v_a_855_;
    }
}
pub unsafe fn l_String_Pos_Raw_instLinearOrderPackage___lam__1___boxed(
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_b_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l_String_Pos_Raw_instLinearOrderPackage___lam__1(v_a_858_, v_b_859_);
    crate::leanh::lean_dec(v_b_859_);
    crate::leanh::lean_dec(v_a_858_);
    return v_res_860_;
}
pub unsafe fn _init_l_String_Pos_Raw_instLinearOrderPackage___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqRaw___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_865_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_865_, 0, v___x_864_);
    return v___f_865_;
}
pub unsafe fn _init_l_String_Pos_Raw_instLinearOrderPackage___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_String_Pos_Raw_instLinearOrderPackage___closed__4;
    v_this_870_ = l_String_Pos_Raw_instLinearOrderPackage___closed__2;
    v___f_871_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__3),
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__3_once),
        _init_l_String_Pos_Raw_instLinearOrderPackage___closed__3,
    );
    v_this_872_ = crate::leanh::lean_box(0);
    v_this_873_ = crate::leanh::lean_box(0);
    v___x_874_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_874_, 0, v_this_873_);
    crate::leanh::lean_ctor_set(v___x_874_, 1, v_this_872_);
    crate::leanh::lean_ctor_set(v___x_874_, 2, v___f_871_);
    crate::leanh::lean_ctor_set(v___x_874_, 3, v_this_870_);
    crate::leanh::lean_ctor_set(v___x_874_, 4, v___x_869_);
    return v___x_874_;
}
pub unsafe fn _init_l_String_Pos_Raw_instLinearOrderPackage___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___f_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_875_ = l_String_Pos_Raw_instLinearOrderPackage___closed__5;
    v___x_876_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__6),
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__6_once),
        _init_l_String_Pos_Raw_instLinearOrderPackage___closed__6,
    );
    v___x_877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_877_, 0, v___x_876_);
    crate::leanh::lean_ctor_set(v___x_877_, 1, v___f_875_);
    return v___x_877_;
}
pub unsafe fn _init_l_String_Pos_Raw_instLinearOrderPackage___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___f_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_878_ = l_String_Pos_Raw_instLinearOrderPackage___closed__1;
    v___f_879_ = l_String_Pos_Raw_instLinearOrderPackage___closed__0;
    v___x_880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__7),
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__7_once),
        _init_l_String_Pos_Raw_instLinearOrderPackage___closed__7,
    );
    v___x_881_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 1, v___f_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 2, v___f_878_);
    return v___x_881_;
}
pub unsafe fn _init_l_String_Pos_Raw_instLinearOrderPackage() -> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__8),
        core::ptr::addr_of_mut!(l_String_Pos_Raw_instLinearOrderPackage___closed__8_once),
        _init_l_String_Pos_Raw_instLinearOrderPackage___closed__8,
    );
    return v___x_882_;
}
pub unsafe fn l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(
    mut v_s_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_884_ =
        crate::leanh::lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    return v___f_884_;
}
pub unsafe fn l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(
    mut v_s_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(v_s_885_);
    crate::leanh::lean_dec_ref(v_s_885_);
    return v_res_886_;
}
pub unsafe fn l_String_Pos_instTransLe(
    mut v_s_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = crate::leanh::lean_box(0);
    return v___x_888_;
}
pub unsafe fn l_String_Pos_instTransLe___boxed(
    mut v_s_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_890_ = l_String_Pos_instTransLe(v_s_889_);
    crate::leanh::lean_dec_ref(v_s_889_);
    return v_res_890_;
}
pub unsafe fn l_String_Pos_instLinearOrderPackage(
    mut v_s_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_892_ = l_String_Pos_Raw_instLinearOrderPackage___closed__0;
    v___f_893_ = l_String_Pos_Raw_instLinearOrderPackage___closed__1;
    v_this_894_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref_n(v_s_891_, 2);
    v_this_895_ = crate::leanh::lean_alloc_closure(
        l_String_instDecidableLePos___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v_this_895_, 0, v_s_891_);
    v_this_896_ = crate::leanh::lean_box(0);
    v___x_897_ = crate::leanh::lean_alloc_closure(
        l_String_instDecidableEqPos___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_897_, 0, v_s_891_);
    v___f_898_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_898_, 0, v___x_897_);
    v___x_899_ = crate::leanh::lean_alloc_closure(
        l_String_instDecidableLtPos___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_899_, 0, v_s_891_);
    crate::leanh::lean_inc_ref(v_this_895_);
    v___f_900_ = crate::leanh::lean_alloc_closure(
        l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_900_, 0, v_this_895_);
    v___x_901_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_901_, 0, v_this_894_);
    crate::leanh::lean_ctor_set(v___x_901_, 1, v_this_896_);
    crate::leanh::lean_ctor_set(v___x_901_, 2, v___f_898_);
    crate::leanh::lean_ctor_set(v___x_901_, 3, v_this_895_);
    crate::leanh::lean_ctor_set(v___x_901_, 4, v___x_899_);
    v___x_902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_902_, 0, v___x_901_);
    crate::leanh::lean_ctor_set(v___x_902_, 1, v___f_900_);
    v___x_903_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_903_, 0, v___x_902_);
    crate::leanh::lean_ctor_set(v___x_903_, 1, v___f_892_);
    crate::leanh::lean_ctor_set(v___x_903_, 2, v___f_893_);
    return v___x_903_;
}
pub unsafe fn l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(
    mut v_s_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_905_ =
        crate::leanh::lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    return v___f_905_;
}
pub unsafe fn l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(
    mut v_s_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(v_s_906_);
    crate::leanh::lean_dec_ref(v_s_906_);
    return v_res_907_;
}
pub unsafe fn l_String_Slice_Pos_instTransLe(
    mut v_s_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = crate::leanh::lean_box(0);
    return v___x_909_;
}
pub unsafe fn l_String_Slice_Pos_instTransLe___boxed(
    mut v_s_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_911_ = l_String_Slice_Pos_instTransLe(v_s_910_);
    crate::leanh::lean_dec_ref(v_s_910_);
    return v_res_911_;
}
pub unsafe fn l_String_Slice_Pos_instLinearOrderPackage(
    mut v_s_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_913_ = l_String_Pos_Raw_instLinearOrderPackage___closed__0;
    v___f_914_ = l_String_Pos_Raw_instLinearOrderPackage___closed__1;
    v_this_915_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref_n(v_s_912_, 2);
    v_this_916_ = crate::leanh::lean_alloc_closure(
        l_String_instDecidableLePos__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v_this_916_, 0, v_s_912_);
    v_this_917_ = crate::leanh::lean_box(0);
    v___x_918_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_instDecidableEqPos___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_918_, 0, v_s_912_);
    v___f_919_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_919_, 0, v___x_918_);
    v___x_920_ = crate::leanh::lean_alloc_closure(
        l_String_instDecidableLtPos__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_920_, 0, v_s_912_);
    crate::leanh::lean_inc_ref(v_this_916_);
    v___f_921_ = crate::leanh::lean_alloc_closure(
        l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_921_, 0, v_this_916_);
    v___x_922_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_922_, 0, v_this_915_);
    crate::leanh::lean_ctor_set(v___x_922_, 1, v_this_917_);
    crate::leanh::lean_ctor_set(v___x_922_, 2, v___f_919_);
    crate::leanh::lean_ctor_set(v___x_922_, 3, v_this_916_);
    crate::leanh::lean_ctor_set(v___x_922_, 4, v___x_920_);
    v___x_923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    crate::leanh::lean_ctor_set(v___x_923_, 1, v___f_921_);
    v___x_924_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
    crate::leanh::lean_ctor_set(v___x_924_, 1, v___f_913_);
    crate::leanh::lean_ctor_set(v___x_924_, 2, v___f_914_);
    return v___x_924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_OrderInstances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_String_Pos_Raw_instTransLe = _init_l_String_Pos_Raw_instTransLe();
    l_String_Pos_Raw_instLinearOrderPackage = _init_l_String_Pos_Raw_instLinearOrderPackage();
    crate::leanh::lean_mark_persistent(l_String_Pos_Raw_instLinearOrderPackage);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_OrderInstances(
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
pub unsafe fn initialize_Init_Data_String_OrderInstances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_PackageFactories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_PackageFactories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_OrderInstances(builtin);
}
