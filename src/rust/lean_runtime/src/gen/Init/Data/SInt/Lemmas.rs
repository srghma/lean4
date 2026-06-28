// Lean compiler output
// Module: Init.Data.SInt.Lemmas
// Imports: Init.Data.Nat.Bitwise.Basic Init.Data.SInt.Basic Init.Data.SInt.Basic Init.Data.BitVec.Basic Init.Data.UInt.Basic Init.Data.BitVec.Lemmas Init.Data.Int.Order Init.ByCases Init.Data.BitVec.Bitblast Init.Data.BitVec.Bootstrap Init.Data.Int.DivMod.Lemmas Init.Data.Int.LemmasAux Init.Data.Int.Pow Init.Data.UInt.Lemmas Init.System.Platform
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::Bitblast::{
    initialize_Init_Data_BitVec_Bitblast, runtime_initialize_Init_Data_BitVec_Bitblast,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_Syntax_node7, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, runtime_initialize_Init_System_Platform,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static l_commandDeclare__int__theorems_____00__closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            99, 111, 109, 109, 97, 110, 100, 68, 101, 99, 108, 97, 114, 101, 95, 105, 110, 116, 95,
            116, 104, 101, 111, 114, 101, 109, 115, 95, 95, 0,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__0_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__0_value)
                as *mut LeanObject,
            4470897265345884150 as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__1_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__2_value: LeanStringObject<8> =
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
static mut l_commandDeclare__int__theorems_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__2_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__2_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__3_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__4_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            100, 101, 99, 108, 97, 114, 101, 95, 105, 110, 116, 95, 116, 104, 101, 111, 114, 101,
            109, 115, 0,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__4_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__5_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_commandDeclare__int__theorems_____00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__6_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__6_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__7_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__8_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__9_value) as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__10_value: LeanStringObject<5> =
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
static mut l_commandDeclare__int__theorems_____00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__10_value)
        as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__10_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__11_value)
        as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__11_value)
                as *mut LeanObject,
            (((1023 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__12_value)
        as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__13_value)
        as *mut LeanObject;
pub static l_commandDeclare__int__theorems_____00__closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_commandDeclare__int__theorems_____00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__14_value)
        as *mut LeanObject;
pub static mut l_commandDeclare__int__theorems____: *mut LeanObject =
    core::ptr::addr_of!(l_commandDeclare__int__theorems_____00__closed__14_value)
        as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value) as *mut LeanObject,17575194138276270420 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value) as *mut LeanObject,2533412339571800130 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value) as *mut LeanObject,7499624980761693169 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value) as *mut LeanObject,3878072352281346923 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 116, 95, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value) as *mut LeanObject,1350029983115203158 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value) as *mut LeanObject,3907549710869165294 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value) as *mut LeanObject,1827444229220621555 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 101, 95, 105, 102, 102, 95, 116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value) as *mut LeanObject,1661142927245337312 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value) as *mut LeanObject,5940551064397964566 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value) as *mut LeanObject,6962862263136859431 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [98, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value) as *mut LeanObject,10300200614825825839 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 134, 148, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value) as *mut LeanObject,17648941618195692764 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 164, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value) as *mut LeanObject,8748957123817046895 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 164, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 148, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,16071506607298534126 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value) as *mut LeanObject,12012343825738880741 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [98, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63: *mut LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value) as *mut LeanObject,10300200614825825839 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,11947561764753763078 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value) as *mut LeanObject,13585030837571646948 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 102, 102, 46, 114, 102, 108, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value) as *mut LeanObject,3546295369065387461 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 116, 95, 105, 102, 102, 95, 116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 108, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value) as *mut LeanObject,707632200809020679 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 60, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value) as *mut LeanObject,6883052497475924672 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [60, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 108, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 108, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,16071506607298534126 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value) as *mut LeanObject,10413004153161948632 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 105, 110, 106, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value) as *mut LeanObject,9312873060023203161 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value) as *mut LeanObject,5677895497334651815 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92: *mut LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,16071506607298534126 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 46, 105, 110, 106, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 106, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,8767050042937596034 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value) as *mut LeanObject,18243930563140520451 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 117, 98, 115, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value) as *mut LeanObject,13050758374263360937 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 100, 111, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value) as *mut LeanObject,6167508377434939095 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 183, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 150, 184, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value) as *mut LeanObject,17342663138809293389 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [111, 102, 66, 105, 116, 86, 101, 99, 95, 105, 110, 106, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value) as *mut LeanObject,13383982971702852061 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value) as *mut LeanObject,5394957827732845164 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 102, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value) as *mut LeanObject,12510029031145868653 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value) as *mut LeanObject,12695378809397736991 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 102, 102, 46, 105, 110, 116, 114, 111, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value) as *mut LeanObject,12124685706703772592 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value) as *mut LeanObject,8689124066155232629 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 105, 110, 116, 114, 111, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value) as *mut LeanObject,10592081902191181482 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 105, 110, 116, 114, 111, 80, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 110, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value) as *mut LeanObject,18291307736269544824 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value) as *mut LeanObject,4405638894356977192 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 99, 97, 115, 101, 115, 80, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value) as *mut LeanObject,1416858759244133794 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value) as *mut LeanObject,12149849828610578618 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value) as *mut LeanObject,5378309054007488965 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 105, 109, 84, 97, 114, 103, 101, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value) as *mut LeanObject,12379583263280086920 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value) as *mut LeanObject,3294379458557754569 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 113, 95, 105, 102, 102, 95, 111, 102, 66, 105, 116, 86, 101, 99, 95, 101, 113, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value) as *mut LeanObject,3171949004442875596 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [111, 102, 66, 105, 116, 86, 101, 99, 95, 105, 110, 106, 46, 115, 121, 109, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 121, 109, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value) as *mut LeanObject,13383982971702852061 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value) as *mut LeanObject,10622583558366744854 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [110, 101, 95, 105, 102, 102, 95, 111, 102, 66, 105, 116, 86, 101, 99, 95, 110, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value) as *mut LeanObject,13620194123125849265 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 160, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value) as *mut LeanObject,6870096354468370040 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 160, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value) as *mut LeanObject,12783917532758215986 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value) as *mut LeanObject,7383208167966365478 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 113, 95, 105, 102, 102, 95, 116, 111, 66, 105, 116, 86, 101, 99, 95, 101, 113, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value) as *mut LeanObject,13040353045680407756 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 105, 110, 106, 46, 115, 121, 109, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190: *mut LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value) as *mut LeanObject,9312873060023203161 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value) as *mut LeanObject,13498314884841943362 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [110, 101, 95, 105, 102, 102, 95, 116, 111, 66, 105, 116, 86, 101, 99, 95, 110, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value) as *mut LeanObject,15277290967324223398 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value) as *mut LeanObject,5353940006376281447 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 46, 110, 111, 116, 95, 105, 102, 102, 95, 110, 111, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 111, 116, 95, 105, 102, 102, 95, 110, 111, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value) as *mut LeanObject,5928360746972917832 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 105, 101, 108, 100, 73, 100, 120, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value) as *mut LeanObject,11762790821414669811 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [50, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value) as *mut LeanObject,1018263045977948327 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 111, 102, 78, 97, 116, 39, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value) as *mut LeanObject,2225313729364741904 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [110, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value) as *mut LeanObject,9980807645604102997 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,8767050042937596034 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value) as *mut LeanObject,2352999024202929854 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [66, 105, 116, 86, 101, 99, 46, 111, 102, 78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222: *mut LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value) as *mut LeanObject,5394957827732845164 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value) as *mut LeanObject,7578295756008745317 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 111, 102, 78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value) as *mut LeanObject,3978485805346465840 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 105, 110, 100, 101, 120, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value) as *mut LeanObject,9160513123679964928 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 95, 105, 110, 100, 101, 120, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 102, 78, 97, 116, 46, 111, 102, 78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value) as *mut LeanObject,14373170258808360993 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 97, 100, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value) as *mut LeanObject,11075853946222974006 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 43, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value) as *mut LeanObject,8601847764421812281 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 117, 98, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value) as *mut LeanObject,2268102815365073163 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 45, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value) as *mut LeanObject,7908490553681470044 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 109, 117, 108, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value) as *mut LeanObject,4077551420002318158 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 42, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value) as *mut LeanObject,14501758599333027494 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 100, 105, 118, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value) as *mut LeanObject,5929967401322673133 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 47, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value) as *mut LeanObject,12719513070702669778 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 100, 105, 118, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 100, 105, 118, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,16071506607298534126 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value) as *mut LeanObject,13573413801138547212 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 109, 111, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value) as *mut LeanObject,14256048511490383488 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 37, 95, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value) as *mut LeanObject,15774053547144697567 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [37, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 114, 101, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value) as *mut LeanObject;
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 114, 101, 109, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value) as *mut LeanObject,16071506607298534126 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value) as *mut LeanObject,5415536550441178218 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value) as *mut LeanObject;
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value) as *mut LeanObject;
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value) as *mut LeanObject,10057000334683702526 as *mut LeanObject] };
static mut l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value) as *mut LeanObject;
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11()
-> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Array_mkArray0(lean_box(0));
    return v___x_1174_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24()
-> *mut LeanObject {
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    v___x_1203_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23;
    v___x_1204_ = l_String_toRawSubstring_x27(v___x_1203_);
    return v___x_1204_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32()
-> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31;
    v___x_1222_ = l_String_toRawSubstring_x27(v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40()
-> *mut LeanObject {
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    v___x_1239_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39;
    v___x_1240_ = l_String_toRawSubstring_x27(v___x_1239_);
    return v___x_1240_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43()
-> *mut LeanObject {
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    v___x_1244_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42;
    v___x_1245_ = l_String_toRawSubstring_x27(v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58()
-> *mut LeanObject {
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    v___x_1271_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57;
    v___x_1272_ = l_String_toRawSubstring_x27(v___x_1271_);
    return v___x_1272_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63()
-> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1280_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62;
    v___x_1281_ = l_String_toRawSubstring_x27(v___x_1280_);
    return v___x_1281_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69()
-> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68;
    v___x_1294_ = l_String_toRawSubstring_x27(v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77()
-> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76;
    v___x_1309_ = l_String_toRawSubstring_x27(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83()
-> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82;
    v___x_1318_ = l_String_toRawSubstring_x27(v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87()
-> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86;
    v___x_1326_ = l_String_toRawSubstring_x27(v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92()
-> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v___x_1333_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91;
    v___x_1334_ = l_String_toRawSubstring_x27(v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99()
-> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98;
    v___x_1348_ = l_String_toRawSubstring_x27(v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111()
-> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110;
    v___x_1372_ = l_String_toRawSubstring_x27(v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118()
-> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    v___x_1387_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71;
    v___x_1388_ = l_String_toRawSubstring_x27(v___x_1387_);
    return v___x_1388_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123()
-> *mut LeanObject {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122;
    v___x_1395_ = l_String_toRawSubstring_x27(v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126()
-> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125;
    v___x_1400_ = l_String_toRawSubstring_x27(v___x_1399_);
    return v___x_1400_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129()
-> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128;
    v___x_1405_ = l_String_toRawSubstring_x27(v___x_1404_);
    return v___x_1405_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144()
-> *mut LeanObject {
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1441_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143;
    v___x_1442_ = l_String_toRawSubstring_x27(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157()
-> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156;
    v___x_1476_ = l_String_toRawSubstring_x27(v___x_1475_);
    return v___x_1476_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167()
-> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166;
    v___x_1500_ = l_String_toRawSubstring_x27(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170()
-> *mut LeanObject {
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    v___x_1504_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169;
    v___x_1505_ = l_String_toRawSubstring_x27(v___x_1504_);
    return v___x_1505_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174()
-> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    v___x_1511_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173;
    v___x_1512_ = l_String_toRawSubstring_x27(v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187()
-> *mut LeanObject {
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1539_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186;
    v___x_1540_ = l_String_toRawSubstring_x27(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190()
-> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189;
    v___x_1545_ = l_String_toRawSubstring_x27(v___x_1544_);
    return v___x_1545_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193()
-> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1550_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192;
    v___x_1551_ = l_String_toRawSubstring_x27(v___x_1550_);
    return v___x_1551_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198()
-> *mut LeanObject {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    v___x_1561_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197;
    v___x_1562_ = l_String_toRawSubstring_x27(v___x_1561_);
    return v___x_1562_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208()
-> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1579_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207;
    v___x_1580_ = l_String_toRawSubstring_x27(v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211()
-> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210;
    v___x_1585_ = l_String_toRawSubstring_x27(v___x_1584_);
    return v___x_1585_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214()
-> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213;
    v___x_1590_ = l_String_toRawSubstring_x27(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216()
-> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59;
    v___x_1594_ = l_String_toRawSubstring_x27(v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219()
-> *mut LeanObject {
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218;
    v___x_1599_ = l_String_toRawSubstring_x27(v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222()
-> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221;
    v___x_1604_ = l_String_toRawSubstring_x27(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228()
-> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    v___x_1616_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227;
    v___x_1617_ = l_String_toRawSubstring_x27(v___x_1616_);
    return v___x_1617_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234()
-> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1628_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233;
    v___x_1629_ = l_String_toRawSubstring_x27(v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240()
-> *mut LeanObject {
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1641_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239;
    v___x_1642_ = l_String_toRawSubstring_x27(v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246()
-> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1650_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245;
    v___x_1651_ = l_String_toRawSubstring_x27(v___x_1650_);
    return v___x_1651_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252()
-> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251;
    v___x_1660_ = l_String_toRawSubstring_x27(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258()
-> *mut LeanObject {
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v___x_1668_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257;
    v___x_1669_ = l_String_toRawSubstring_x27(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264()
-> *mut LeanObject {
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_1677_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263;
    v___x_1678_ = l_String_toRawSubstring_x27(v___x_1677_);
    return v___x_1678_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268()
-> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267;
    v___x_1686_ = l_String_toRawSubstring_x27(v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274()
-> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273;
    v___x_1695_ = l_String_toRawSubstring_x27(v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(
    mut v_x_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_a_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    v___x_1710_ = l_commandDeclare__int__theorems_____00__closed__1;
    lean_inc(v_x_1707_);
    v___x_1711_ = l_Lean_Syntax_isOfKind(v_x_1707_, v___x_1710_);
    if v___x_1711_ == 0 {
        let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1707_);
        v___x_1712_ = lean_box(1);
        v___x_1713_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1713_, 0, v___x_1712_);
        lean_ctor_set(v___x_1713_, 1, v_a_1709_);
        return v___x_1713_;
    } else {
        let mut v_ref_1714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: u8 = 0;
        let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1714_ = lean_ctor_get(v_a_1708_, 5);
        v___x_1715_ = lean_unsigned_to_nat(1);
        v___x_1716_ = l_Lean_Syntax_getArg(v_x_1707_, v___x_1715_);
        v___x_1717_ = lean_unsigned_to_nat(2);
        v___x_1718_ = l_Lean_Syntax_getArg(v_x_1707_, v___x_1717_);
        lean_dec(v_x_1707_);
        v___x_1719_ = 0;
        v___x_1720_ = l_Lean_SourceInfo_fromRef(v_ref_1714_, v___x_1719_);
        v___x_1721_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1;
        v___x_1722_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5;
        v___x_1723_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6;
        lean_inc_n(v___x_1720_, 306);
        v___x_1724_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1724_, 0, v___x_1720_);
        lean_ctor_set(v___x_1724_, 1, v___x_1722_);
        lean_inc_n(v___x_1716_, 2);
        v___x_1725_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1723_, v___x_1724_, v___x_1716_);
        v___x_1726_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8;
        v___x_1727_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10;
        v___x_1728_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11);
        v___x_1729_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1729_, 0, v___x_1720_);
        lean_ctor_set(v___x_1729_, 1, v___x_1721_);
        lean_ctor_set(v___x_1729_, 2, v___x_1728_);
        v___x_1730_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14;
        v___x_1731_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15;
        v___x_1732_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1732_, 0, v___x_1720_);
        lean_ctor_set(v___x_1732_, 1, v___x_1731_);
        v___x_1733_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17;
        v___x_1734_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19;
        lean_inc_ref_n(v___x_1729_, 70);
        v___x_1735_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1734_, v___x_1729_);
        v___x_1736_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22;
        v___x_1737_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24);
        v___x_1738_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25;
        v___x_1739_ = lean_box(0);
        v___x_1740_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1740_, 0, v___x_1720_);
        lean_ctor_set(v___x_1740_, 1, v___x_1737_);
        lean_ctor_set(v___x_1740_, 2, v___x_1738_);
        lean_ctor_set(v___x_1740_, 3, v___x_1739_);
        v___x_1741_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1736_, v___x_1740_, v___x_1729_);
        lean_inc(v___x_1735_);
        v___x_1742_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1733_, v___x_1735_, v___x_1741_);
        lean_inc(v___x_1742_);
        v___x_1743_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1742_);
        v___x_1744_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26;
        v___x_1745_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1745_, 0, v___x_1720_);
        lean_ctor_set(v___x_1745_, 1, v___x_1744_);
        lean_inc_ref_n(v___x_1745_, 3);
        lean_inc_ref_n(v___x_1732_, 2);
        v___x_1746_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1730_,
            v___x_1732_,
            v___x_1743_,
            v___x_1745_,
        );
        v___x_1747_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1746_);
        v___x_1748_ = l_Lean_Syntax_node7(
            v___x_1720_,
            v___x_1727_,
            v___x_1729_,
            v___x_1747_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_1749_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27;
        v___x_1750_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28;
        v___x_1751_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1751_, 0, v___x_1720_);
        lean_ctor_set(v___x_1751_, 1, v___x_1749_);
        v___x_1752_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30;
        v___x_1753_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32);
        v___x_1754_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33;
        v___x_1755_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1755_, 0, v___x_1720_);
        lean_ctor_set(v___x_1755_, 1, v___x_1753_);
        lean_ctor_set(v___x_1755_, 2, v___x_1754_);
        lean_ctor_set(v___x_1755_, 3, v___x_1739_);
        v___x_1756_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1755_, v___x_1729_);
        v___x_1757_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35;
        v___x_1758_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37;
        v___x_1759_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38;
        v___x_1760_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1760_, 0, v___x_1720_);
        lean_ctor_set(v___x_1760_, 1, v___x_1759_);
        v___x_1761_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40);
        v___x_1762_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41;
        v___x_1763_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1763_, 0, v___x_1720_);
        lean_ctor_set(v___x_1763_, 1, v___x_1761_);
        lean_ctor_set(v___x_1763_, 2, v___x_1762_);
        lean_ctor_set(v___x_1763_, 3, v___x_1739_);
        v___x_1764_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43);
        v___x_1765_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44;
        v___x_1766_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1766_, 0, v___x_1720_);
        lean_ctor_set(v___x_1766_, 1, v___x_1764_);
        lean_ctor_set(v___x_1766_, 2, v___x_1765_);
        lean_ctor_set(v___x_1766_, 3, v___x_1739_);
        lean_inc_ref_n(v___x_1766_, 10);
        lean_inc_ref_n(v___x_1763_, 10);
        v___x_1767_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_1763_, v___x_1766_);
        v___x_1768_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45;
        v___x_1769_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1769_, 0, v___x_1720_);
        lean_ctor_set(v___x_1769_, 1, v___x_1768_);
        lean_inc_ref_n(v___x_1769_, 17);
        v___x_1770_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_1769_, v___x_1716_);
        v___x_1771_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46;
        v___x_1772_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1772_, 0, v___x_1720_);
        lean_ctor_set(v___x_1772_, 1, v___x_1771_);
        lean_inc_ref_n(v___x_1772_, 2);
        lean_inc(v___x_1767_);
        lean_inc_ref_n(v___x_1760_, 2);
        v___x_1773_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1758_,
            v___x_1760_,
            v___x_1767_,
            v___x_1770_,
            v___x_1772_,
        );
        v___x_1774_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1773_);
        v___x_1775_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48;
        v___x_1776_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50;
        v___x_1777_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52;
        v___x_1778_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53;
        v___x_1779_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1779_, 0, v___x_1720_);
        lean_ctor_set(v___x_1779_, 1, v___x_1778_);
        v___x_1780_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1777_,
            v___x_1763_,
            v___x_1779_,
            v___x_1766_,
        );
        v___x_1781_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54;
        v___x_1782_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1782_, 0, v___x_1720_);
        lean_ctor_set(v___x_1782_, 1, v___x_1781_);
        v___x_1783_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56;
        v___x_1784_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58);
        v___x_1785_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61;
        v___x_1786_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1786_, 0, v___x_1720_);
        lean_ctor_set(v___x_1786_, 1, v___x_1784_);
        lean_ctor_set(v___x_1786_, 2, v___x_1785_);
        lean_ctor_set(v___x_1786_, 3, v___x_1739_);
        v___x_1787_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63);
        v___x_1788_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64;
        v___x_1789_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1789_, 0, v___x_1720_);
        lean_ctor_set(v___x_1789_, 1, v___x_1787_);
        lean_ctor_set(v___x_1789_, 2, v___x_1788_);
        lean_ctor_set(v___x_1789_, 3, v___x_1739_);
        lean_inc_ref_n(v___x_1789_, 5);
        v___x_1790_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1789_);
        lean_inc_n(v___x_1790_, 3);
        v___x_1791_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_1786_, v___x_1790_);
        lean_inc_ref_n(v___x_1782_, 7);
        v___x_1792_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1780_,
            v___x_1782_,
            v___x_1791_,
        );
        v___x_1793_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1792_);
        lean_inc_n(v___x_1774_, 9);
        v___x_1794_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_1793_);
        v___x_1795_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66;
        v___x_1796_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67;
        v___x_1797_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1797_, 0, v___x_1720_);
        lean_ctor_set(v___x_1797_, 1, v___x_1796_);
        v___x_1798_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69);
        v___x_1799_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71;
        v___x_1800_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72;
        v___x_1801_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1801_, 0, v___x_1720_);
        lean_ctor_set(v___x_1801_, 1, v___x_1798_);
        lean_ctor_set(v___x_1801_, 2, v___x_1800_);
        lean_ctor_set(v___x_1801_, 3, v___x_1739_);
        v___x_1802_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75;
        v___x_1803_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1802_, v___x_1729_, v___x_1729_);
        lean_inc_n(v___x_1803_, 7);
        lean_inc_ref_n(v___x_1797_, 7);
        v___x_1804_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_1801_,
            v___x_1803_,
            v___x_1729_,
        );
        lean_inc(v___x_1804_);
        lean_inc_ref_n(v___x_1751_, 14);
        v___x_1805_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1756_,
            v___x_1794_,
            v___x_1804_,
        );
        lean_inc_n(v___x_1748_, 3);
        v___x_1806_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1748_, v___x_1805_);
        v___x_1807_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77);
        v___x_1808_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78;
        v___x_1809_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1809_, 0, v___x_1720_);
        lean_ctor_set(v___x_1809_, 1, v___x_1807_);
        lean_ctor_set(v___x_1809_, 2, v___x_1808_);
        lean_ctor_set(v___x_1809_, 3, v___x_1739_);
        v___x_1810_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1809_, v___x_1729_);
        v___x_1811_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80;
        v___x_1812_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81;
        v___x_1813_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1813_, 0, v___x_1720_);
        lean_ctor_set(v___x_1813_, 1, v___x_1812_);
        v___x_1814_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1811_,
            v___x_1763_,
            v___x_1813_,
            v___x_1766_,
        );
        v___x_1815_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83);
        v___x_1816_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85;
        v___x_1817_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1817_, 0, v___x_1720_);
        lean_ctor_set(v___x_1817_, 1, v___x_1815_);
        lean_ctor_set(v___x_1817_, 2, v___x_1816_);
        lean_ctor_set(v___x_1817_, 3, v___x_1739_);
        v___x_1818_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_1817_, v___x_1790_);
        v___x_1819_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1814_,
            v___x_1782_,
            v___x_1818_,
        );
        v___x_1820_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1819_);
        v___x_1821_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_1820_);
        v___x_1822_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1810_,
            v___x_1821_,
            v___x_1804_,
        );
        v___x_1823_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1748_, v___x_1822_);
        v___x_1824_ = l_Lean_Syntax_node7(
            v___x_1720_,
            v___x_1727_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_1825_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87);
        v___x_1826_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88;
        v___x_1827_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1827_, 0, v___x_1720_);
        lean_ctor_set(v___x_1827_, 1, v___x_1825_);
        lean_ctor_set(v___x_1827_, 2, v___x_1826_);
        lean_ctor_set(v___x_1827_, 3, v___x_1739_);
        v___x_1828_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1827_, v___x_1729_);
        v___x_1829_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90;
        v___x_1830_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92);
        v___x_1831_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93;
        v___x_1832_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1832_, 0, v___x_1720_);
        lean_ctor_set(v___x_1832_, 1, v___x_1830_);
        lean_ctor_set(v___x_1832_, 2, v___x_1831_);
        lean_ctor_set(v___x_1832_, 3, v___x_1739_);
        v___x_1833_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94;
        v___x_1834_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1834_, 0, v___x_1720_);
        lean_ctor_set(v___x_1834_, 1, v___x_1833_);
        lean_inc_ref_n(v___x_1834_, 9);
        lean_inc_ref_n(v___x_1832_, 4);
        v___x_1835_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_1832_,
            v___x_1834_,
            v___x_1789_,
        );
        v___x_1836_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_1763_,
            v___x_1834_,
            v___x_1766_,
        );
        lean_inc_n(v___x_1836_, 3);
        lean_inc(v___x_1835_);
        v___x_1837_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1835_,
            v___x_1782_,
            v___x_1836_,
        );
        v___x_1838_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1837_);
        v___x_1839_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_1838_);
        v___x_1840_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96;
        v___x_1841_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97;
        v___x_1842_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1842_, 0, v___x_1720_);
        lean_ctor_set(v___x_1842_, 1, v___x_1841_);
        v___x_1843_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99);
        v___x_1844_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101;
        v___x_1845_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1845_, 0, v___x_1720_);
        lean_ctor_set(v___x_1845_, 1, v___x_1843_);
        lean_ctor_set(v___x_1845_, 2, v___x_1844_);
        lean_ctor_set(v___x_1845_, 3, v___x_1739_);
        v___x_1846_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102;
        v___x_1847_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1847_, 0, v___x_1720_);
        lean_ctor_set(v___x_1847_, 1, v___x_1846_);
        v___x_1848_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104;
        v___x_1849_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106;
        v___x_1850_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107;
        v___x_1851_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1851_, 0, v___x_1720_);
        lean_ctor_set(v___x_1851_, 1, v___x_1850_);
        v___x_1852_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109;
        v___x_1853_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111);
        v___x_1854_ = lean_box(0);
        v___x_1855_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1855_, 0, v___x_1720_);
        lean_ctor_set(v___x_1855_, 1, v___x_1853_);
        lean_ctor_set(v___x_1855_, 2, v___x_1854_);
        lean_ctor_set(v___x_1855_, 3, v___x_1739_);
        v___x_1856_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1852_, v___x_1855_);
        lean_inc(v___x_1856_);
        lean_inc_ref(v___x_1851_);
        v___x_1857_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1849_, v___x_1851_, v___x_1856_);
        v___x_1858_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113;
        v___x_1859_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115;
        v___x_1860_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116;
        v___x_1861_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1861_, 0, v___x_1720_);
        lean_ctor_set(v___x_1861_, 1, v___x_1860_);
        v___x_1862_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1859_, v___x_1861_, v___x_1856_);
        v___x_1863_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117;
        v___x_1864_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1864_, 0, v___x_1720_);
        lean_ctor_set(v___x_1864_, 1, v___x_1863_);
        v___x_1865_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118);
        v___x_1866_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119;
        v___x_1867_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1867_, 0, v___x_1720_);
        lean_ctor_set(v___x_1867_, 1, v___x_1865_);
        lean_ctor_set(v___x_1867_, 2, v___x_1866_);
        lean_ctor_set(v___x_1867_, 3, v___x_1739_);
        lean_inc_ref(v___x_1867_);
        v___x_1868_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1867_);
        v___x_1869_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1858_,
            v___x_1862_,
            v___x_1864_,
            v___x_1868_,
        );
        v___x_1870_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120;
        v___x_1871_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1871_, 0, v___x_1720_);
        lean_ctor_set(v___x_1871_, 1, v___x_1870_);
        lean_inc_ref_n(v___x_1871_, 10);
        lean_inc_n(v___x_1857_, 9);
        v___x_1872_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_1869_,
            v___x_1871_,
        );
        lean_inc_ref(v___x_1847_);
        v___x_1873_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1721_,
            v___x_1845_,
            v___x_1847_,
            v___x_1872_,
        );
        v___x_1874_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121;
        v___x_1875_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1875_, 0, v___x_1720_);
        lean_ctor_set(v___x_1875_, 1, v___x_1874_);
        v___x_1876_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1840_,
            v___x_1842_,
            v___x_1873_,
            v___x_1875_,
        );
        v___x_1877_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_1876_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_1878_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1828_,
            v___x_1839_,
            v___x_1877_,
        );
        lean_inc_n(v___x_1824_, 3);
        v___x_1879_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1824_, v___x_1878_);
        v___x_1880_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123);
        v___x_1881_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124;
        v___x_1882_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1882_, 0, v___x_1720_);
        lean_ctor_set(v___x_1882_, 1, v___x_1880_);
        lean_ctor_set(v___x_1882_, 2, v___x_1881_);
        lean_ctor_set(v___x_1882_, 3, v___x_1739_);
        lean_inc_ref(v___x_1882_);
        v___x_1883_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1882_, v___x_1729_);
        v___x_1884_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126);
        v___x_1885_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127;
        v___x_1886_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1886_, 0, v___x_1720_);
        lean_ctor_set(v___x_1886_, 1, v___x_1884_);
        lean_ctor_set(v___x_1886_, 2, v___x_1885_);
        lean_ctor_set(v___x_1886_, 3, v___x_1739_);
        v___x_1887_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1718_);
        v___x_1888_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_1886_, v___x_1887_);
        v___x_1889_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_1769_, v___x_1888_);
        v___x_1890_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1758_,
            v___x_1760_,
            v___x_1767_,
            v___x_1889_,
            v___x_1772_,
        );
        v___x_1891_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1890_);
        v___x_1892_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129);
        v___x_1893_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130;
        v___x_1894_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1894_, 0, v___x_1720_);
        lean_ctor_set(v___x_1894_, 1, v___x_1892_);
        lean_ctor_set(v___x_1894_, 2, v___x_1893_);
        lean_ctor_set(v___x_1894_, 3, v___x_1739_);
        v___x_1895_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1763_);
        lean_inc_ref(v___x_1894_);
        v___x_1896_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_1894_, v___x_1895_);
        v___x_1897_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1766_);
        v___x_1898_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_1894_, v___x_1897_);
        lean_inc(v___x_1898_);
        lean_inc(v___x_1896_);
        v___x_1899_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_1896_,
            v___x_1834_,
            v___x_1898_,
        );
        lean_inc(v___x_1899_);
        v___x_1900_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1899_,
            v___x_1782_,
            v___x_1836_,
        );
        v___x_1901_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1900_);
        lean_inc_n(v___x_1891_, 2);
        v___x_1902_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1891_, v___x_1901_);
        v___x_1903_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132;
        v___x_1904_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133;
        v___x_1905_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1905_, 0, v___x_1720_);
        lean_ctor_set(v___x_1905_, 1, v___x_1904_);
        v___x_1906_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136;
        v___x_1907_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138;
        v___x_1908_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140;
        v___x_1909_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141;
        v___x_1910_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142;
        v___x_1911_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1911_, 0, v___x_1720_);
        lean_ctor_set(v___x_1911_, 1, v___x_1909_);
        v___x_1912_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144);
        v___x_1913_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146;
        v___x_1914_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1914_, 0, v___x_1720_);
        lean_ctor_set(v___x_1914_, 1, v___x_1912_);
        lean_ctor_set(v___x_1914_, 2, v___x_1913_);
        lean_ctor_set(v___x_1914_, 3, v___x_1739_);
        v___x_1915_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1910_, v___x_1911_, v___x_1914_);
        v___x_1916_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147;
        v___x_1917_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1917_, 0, v___x_1720_);
        lean_ctor_set(v___x_1917_, 1, v___x_1916_);
        v___x_1918_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148;
        v___x_1919_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149;
        v___x_1920_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150;
        v___x_1921_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1921_, 0, v___x_1720_);
        lean_ctor_set(v___x_1921_, 1, v___x_1919_);
        v___x_1922_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153;
        v___x_1923_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155;
        v___x_1924_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157);
        v___x_1925_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158;
        v___x_1926_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1926_, 0, v___x_1720_);
        lean_ctor_set(v___x_1926_, 1, v___x_1924_);
        lean_ctor_set(v___x_1926_, 2, v___x_1925_);
        lean_ctor_set(v___x_1926_, 3, v___x_1739_);
        lean_inc_ref(v___x_1926_);
        v___x_1927_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1923_, v___x_1926_);
        v___x_1928_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1922_, v___x_1927_);
        v___x_1929_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1928_);
        v___x_1930_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1920_,
            v___x_1921_,
            v___x_1929_,
            v___x_1729_,
        );
        v___x_1931_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159;
        v___x_1932_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1932_, 0, v___x_1720_);
        lean_ctor_set(v___x_1932_, 1, v___x_1931_);
        v___x_1933_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160;
        v___x_1934_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161;
        v___x_1935_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1935_, 0, v___x_1720_);
        lean_ctor_set(v___x_1935_, 1, v___x_1933_);
        v___x_1936_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163;
        v___x_1937_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1936_, v___x_1729_, v___x_1926_);
        v___x_1938_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1937_);
        v___x_1939_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1934_,
            v___x_1935_,
            v___x_1938_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_1940_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165;
        v___x_1941_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1941_, 0, v___x_1720_);
        lean_ctor_set(v___x_1941_, 1, v___x_1799_);
        v___x_1942_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1940_, v___x_1941_);
        lean_inc_ref(v___x_1932_);
        v___x_1943_ = l_Lean_Syntax_node5(
            v___x_1720_,
            v___x_1721_,
            v___x_1930_,
            v___x_1932_,
            v___x_1939_,
            v___x_1932_,
            v___x_1942_,
        );
        v___x_1944_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1907_, v___x_1943_);
        v___x_1945_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1906_, v___x_1944_);
        v___x_1946_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1918_,
            v___x_1851_,
            v___x_1945_,
            v___x_1871_,
        );
        v___x_1947_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1908_,
            v___x_1915_,
            v___x_1917_,
            v___x_1946_,
        );
        v___x_1948_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1947_);
        v___x_1949_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1907_, v___x_1948_);
        v___x_1950_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1906_, v___x_1949_);
        lean_inc_ref(v___x_1905_);
        v___x_1951_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1903_, v___x_1905_, v___x_1950_);
        v___x_1952_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_1951_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_1953_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1883_,
            v___x_1902_,
            v___x_1952_,
        );
        v___x_1954_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1824_, v___x_1953_);
        v___x_1955_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167);
        v___x_1956_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168;
        v___x_1957_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1957_, 0, v___x_1720_);
        lean_ctor_set(v___x_1957_, 1, v___x_1955_);
        lean_ctor_set(v___x_1957_, 2, v___x_1956_);
        lean_ctor_set(v___x_1957_, 3, v___x_1739_);
        v___x_1958_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1957_, v___x_1729_);
        v___x_1959_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1836_,
            v___x_1782_,
            v___x_1899_,
        );
        v___x_1960_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1959_);
        v___x_1961_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1891_, v___x_1960_);
        v___x_1962_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170);
        v___x_1963_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172;
        v___x_1964_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1964_, 0, v___x_1720_);
        lean_ctor_set(v___x_1964_, 1, v___x_1962_);
        lean_ctor_set(v___x_1964_, 2, v___x_1963_);
        lean_ctor_set(v___x_1964_, 3, v___x_1739_);
        v___x_1965_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_1964_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_1966_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1958_,
            v___x_1961_,
            v___x_1965_,
        );
        v___x_1967_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1824_, v___x_1966_);
        v___x_1968_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174);
        v___x_1969_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175;
        v___x_1970_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1970_, 0, v___x_1720_);
        lean_ctor_set(v___x_1970_, 1, v___x_1968_);
        lean_ctor_set(v___x_1970_, 2, v___x_1969_);
        lean_ctor_set(v___x_1970_, 3, v___x_1739_);
        v___x_1971_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_1970_, v___x_1729_);
        v___x_1972_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177;
        v___x_1973_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178;
        v___x_1974_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1974_, 0, v___x_1720_);
        lean_ctor_set(v___x_1974_, 1, v___x_1973_);
        lean_inc_ref_n(v___x_1974_, 2);
        v___x_1975_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1972_,
            v___x_1763_,
            v___x_1974_,
            v___x_1766_,
        );
        v___x_1976_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1972_,
            v___x_1896_,
            v___x_1974_,
            v___x_1898_,
        );
        lean_inc(v___x_1975_);
        v___x_1977_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1975_,
            v___x_1782_,
            v___x_1976_,
        );
        v___x_1978_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_1977_);
        v___x_1979_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1891_, v___x_1978_);
        v___x_1980_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179;
        v___x_1981_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180;
        v___x_1982_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1982_, 0, v___x_1720_);
        lean_ctor_set(v___x_1982_, 1, v___x_1980_);
        v___x_1983_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182;
        v___x_1984_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1983_, v___x_1729_);
        v___x_1985_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183;
        v___x_1986_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1986_, 0, v___x_1720_);
        lean_ctor_set(v___x_1986_, 1, v___x_1985_);
        v___x_1987_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185;
        v___x_1988_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1987_,
            v___x_1729_,
            v___x_1729_,
            v___x_1882_,
        );
        v___x_1989_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1988_);
        v___x_1990_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1721_,
            v___x_1986_,
            v___x_1989_,
            v___x_1745_,
        );
        lean_inc_ref(v___x_1982_);
        v___x_1991_ = l_Lean_Syntax_node6(
            v___x_1720_,
            v___x_1981_,
            v___x_1982_,
            v___x_1984_,
            v___x_1729_,
            v___x_1729_,
            v___x_1990_,
            v___x_1729_,
        );
        v___x_1992_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_1991_);
        v___x_1993_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1907_, v___x_1992_);
        v___x_1994_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1906_, v___x_1993_);
        v___x_1995_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1903_, v___x_1905_, v___x_1994_);
        v___x_1996_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_1995_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_1997_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_1971_,
            v___x_1979_,
            v___x_1996_,
        );
        v___x_1998_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1824_, v___x_1997_);
        v___x_1999_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187);
        v___x_2000_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188;
        v___x_2001_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2001_, 0, v___x_1720_);
        lean_ctor_set(v___x_2001_, 1, v___x_1999_);
        lean_ctor_set(v___x_2001_, 2, v___x_2000_);
        lean_ctor_set(v___x_2001_, 3, v___x_1739_);
        lean_inc_ref(v___x_2001_);
        v___x_2002_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2001_, v___x_1729_);
        v___x_2003_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1836_,
            v___x_1782_,
            v___x_1835_,
        );
        v___x_2004_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2003_);
        v___x_2005_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2004_);
        v___x_2006_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190);
        v___x_2007_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191;
        v___x_2008_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2008_, 0, v___x_1720_);
        lean_ctor_set(v___x_2008_, 1, v___x_2006_);
        lean_ctor_set(v___x_2008_, 2, v___x_2007_);
        lean_ctor_set(v___x_2008_, 3, v___x_1739_);
        v___x_2009_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_2008_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_2010_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2002_,
            v___x_2005_,
            v___x_2009_,
        );
        v___x_2011_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1748_, v___x_2010_);
        v___x_2012_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193);
        v___x_2013_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194;
        v___x_2014_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2014_, 0, v___x_1720_);
        lean_ctor_set(v___x_2014_, 1, v___x_2012_);
        lean_ctor_set(v___x_2014_, 2, v___x_2013_);
        lean_ctor_set(v___x_2014_, 3, v___x_1739_);
        v___x_2015_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2014_, v___x_1729_);
        v___x_2016_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1972_,
            v___x_1832_,
            v___x_1974_,
            v___x_1789_,
        );
        v___x_2017_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1776_,
            v___x_1975_,
            v___x_1782_,
            v___x_2016_,
        );
        v___x_2018_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2017_);
        v___x_2019_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2018_);
        v___x_2020_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196;
        v___x_2021_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198);
        v___x_2022_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201;
        v___x_2023_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2023_, 0, v___x_1720_);
        lean_ctor_set(v___x_2023_, 1, v___x_2021_);
        lean_ctor_set(v___x_2023_, 2, v___x_2022_);
        lean_ctor_set(v___x_2023_, 3, v___x_1739_);
        v___x_2024_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202;
        v___x_2025_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2025_, 0, v___x_1720_);
        lean_ctor_set(v___x_2025_, 1, v___x_2024_);
        v___x_2026_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204;
        v___x_2027_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205;
        v___x_2028_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2028_, 0, v___x_1720_);
        lean_ctor_set(v___x_2028_, 1, v___x_2027_);
        v___x_2029_ = l_Lean_Syntax_node1(v___x_1720_, v___x_2026_, v___x_2028_);
        lean_inc_ref_n(v___x_2025_, 5);
        v___x_2030_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2023_,
            v___x_2025_,
            v___x_2029_,
        );
        v___x_2031_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2001_);
        v___x_2032_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2030_, v___x_2031_);
        v___x_2033_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_2032_,
            v___x_1803_,
            v___x_1729_,
        );
        v___x_2034_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2015_,
            v___x_2019_,
            v___x_2033_,
        );
        v___x_2035_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_1748_, v___x_2034_);
        v___x_2036_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206;
        v___x_2037_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_2036_,
            v___x_1982_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_2038_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1733_, v___x_1735_, v___x_2037_);
        lean_inc(v___x_2038_);
        v___x_2039_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2038_);
        v___x_2040_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1730_,
            v___x_1732_,
            v___x_2039_,
            v___x_1745_,
        );
        v___x_2041_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2040_);
        v___x_2042_ = l_Lean_Syntax_node7(
            v___x_1720_,
            v___x_1727_,
            v___x_1729_,
            v___x_2041_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_2043_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208);
        v___x_2044_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209;
        v___x_2045_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2045_, 0, v___x_1720_);
        lean_ctor_set(v___x_2045_, 1, v___x_2043_);
        lean_ctor_set(v___x_2045_, 2, v___x_2044_);
        lean_ctor_set(v___x_2045_, 3, v___x_1739_);
        v___x_2046_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2045_, v___x_1729_);
        v___x_2047_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211);
        v___x_2048_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212;
        v___x_2049_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2049_, 0, v___x_1720_);
        lean_ctor_set(v___x_2049_, 1, v___x_2047_);
        lean_ctor_set(v___x_2049_, 2, v___x_2048_);
        lean_ctor_set(v___x_2049_, 3, v___x_1739_);
        lean_inc_ref(v___x_2049_);
        v___x_2050_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2049_);
        v___x_2051_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214);
        v___x_2052_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215;
        v___x_2053_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2053_, 0, v___x_1720_);
        lean_ctor_set(v___x_2053_, 1, v___x_2051_);
        lean_ctor_set(v___x_2053_, 2, v___x_2052_);
        lean_ctor_set(v___x_2053_, 3, v___x_1739_);
        v___x_2054_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_1769_, v___x_2053_);
        lean_inc_n(v___x_2050_, 2);
        v___x_2055_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1758_,
            v___x_1760_,
            v___x_2050_,
            v___x_2054_,
            v___x_1772_,
        );
        v___x_2056_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2055_);
        v___x_2057_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216);
        v___x_2058_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217;
        v___x_2059_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2059_, 0, v___x_1720_);
        lean_ctor_set(v___x_2059_, 1, v___x_2057_);
        lean_ctor_set(v___x_2059_, 2, v___x_2058_);
        lean_ctor_set(v___x_2059_, 3, v___x_1739_);
        v___x_2060_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219);
        v___x_2061_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220;
        v___x_2062_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2062_, 0, v___x_1720_);
        lean_ctor_set(v___x_2062_, 1, v___x_2060_);
        lean_ctor_set(v___x_2062_, 2, v___x_2061_);
        lean_ctor_set(v___x_2062_, 3, v___x_1739_);
        v___x_2063_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2062_, v___x_2050_);
        v___x_2064_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2063_,
            v___x_1871_,
        );
        v___x_2065_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2064_);
        lean_inc_ref_n(v___x_2059_, 6);
        v___x_2066_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2059_, v___x_2065_);
        v___x_2067_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222);
        v___x_2068_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223;
        v___x_2069_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2069_, 0, v___x_1720_);
        lean_ctor_set(v___x_2069_, 1, v___x_2067_);
        lean_ctor_set(v___x_2069_, 2, v___x_2068_);
        lean_ctor_set(v___x_2069_, 3, v___x_1739_);
        v___x_2070_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225;
        v___x_2071_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226;
        v___x_2072_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2072_, 0, v___x_1720_);
        lean_ctor_set(v___x_2072_, 1, v___x_2071_);
        v___x_2073_ = l_Lean_Syntax_node1(v___x_1720_, v___x_2070_, v___x_2072_);
        v___x_2074_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_2073_, v___x_2049_);
        v___x_2075_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2069_, v___x_2074_);
        v___x_2076_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2066_,
            v___x_1834_,
            v___x_2075_,
        );
        v___x_2077_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2076_);
        lean_inc(v___x_2056_);
        v___x_2078_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_2056_, v___x_2077_);
        v___x_2079_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_1867_,
            v___x_1871_,
        );
        v___x_2080_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1795_,
            v___x_1797_,
            v___x_2079_,
            v___x_1803_,
            v___x_1729_,
        );
        lean_inc_n(v___x_2080_, 6);
        v___x_2081_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2046_,
            v___x_2078_,
            v___x_2080_,
        );
        v___x_2082_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2042_, v___x_2081_);
        v___x_2083_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1721_,
            v___x_2038_,
            v___x_1847_,
            v___x_1742_,
        );
        v___x_2084_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1730_,
            v___x_1732_,
            v___x_2083_,
            v___x_1745_,
        );
        v___x_2085_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2084_);
        lean_inc(v___x_2085_);
        v___x_2086_ = l_Lean_Syntax_node7(
            v___x_1720_,
            v___x_1727_,
            v___x_1729_,
            v___x_2085_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_2087_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228);
        v___x_2088_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229;
        v___x_2089_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2089_, 0, v___x_1720_);
        lean_ctor_set(v___x_2089_, 1, v___x_2087_);
        lean_ctor_set(v___x_2089_, 2, v___x_2088_);
        lean_ctor_set(v___x_2089_, 3, v___x_1739_);
        v___x_2090_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2089_, v___x_1729_);
        v___x_2091_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231;
        v___x_2092_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232;
        v___x_2093_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2093_, 0, v___x_1720_);
        lean_ctor_set(v___x_2093_, 1, v___x_2092_);
        v___x_2094_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234);
        v___x_2095_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236;
        v___x_2096_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2096_, 0, v___x_1720_);
        lean_ctor_set(v___x_2096_, 1, v___x_2094_);
        lean_ctor_set(v___x_2096_, 2, v___x_2095_);
        lean_ctor_set(v___x_2096_, 3, v___x_1739_);
        v___x_2097_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2096_, v___x_2050_);
        lean_inc(v___x_2097_);
        v___x_2098_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2097_,
            v___x_1871_,
        );
        v___x_2099_ = l_Lean_Syntax_node2(v___x_1720_, v___x_2091_, v___x_2093_, v___x_2098_);
        v___x_2100_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2099_,
            v___x_1871_,
        );
        v___x_2101_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2100_);
        v___x_2102_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2059_, v___x_2101_);
        v___x_2103_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2102_,
            v___x_1834_,
            v___x_2097_,
        );
        v___x_2104_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2103_);
        v___x_2105_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_2056_, v___x_2104_);
        v___x_2106_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2090_,
            v___x_2105_,
            v___x_2080_,
        );
        v___x_2107_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2086_, v___x_2106_);
        v___x_2108_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237;
        v___x_2109_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238;
        v___x_2110_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2110_, 0, v___x_1720_);
        lean_ctor_set(v___x_2110_, 1, v___x_2108_);
        v___x_2111_ = l_Lean_Syntax_node1(v___x_1720_, v___x_2109_, v___x_2110_);
        v___x_2112_ = l_Lean_Syntax_node1(v___x_1720_, v___x_1721_, v___x_2111_);
        v___x_2113_ = l_Lean_Syntax_node7(
            v___x_1720_,
            v___x_1727_,
            v___x_1729_,
            v___x_2085_,
            v___x_1729_,
            v___x_2112_,
            v___x_1729_,
            v___x_1729_,
            v___x_1729_,
        );
        v___x_2114_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240);
        v___x_2115_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241;
        v___x_2116_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2116_, 0, v___x_1720_);
        lean_ctor_set(v___x_2116_, 1, v___x_2114_);
        lean_ctor_set(v___x_2116_, 2, v___x_2115_);
        lean_ctor_set(v___x_2116_, 3, v___x_1739_);
        v___x_2117_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2116_, v___x_1729_);
        v___x_2118_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243;
        v___x_2119_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244;
        v___x_2120_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2120_, 0, v___x_1720_);
        lean_ctor_set(v___x_2120_, 1, v___x_2119_);
        lean_inc_ref(v___x_2120_);
        v___x_2121_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2118_,
            v___x_1763_,
            v___x_2120_,
            v___x_1766_,
        );
        v___x_2122_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2121_,
            v___x_1871_,
        );
        v___x_2123_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2122_,
            v___x_2025_,
            v___x_2059_,
        );
        v___x_2124_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2118_,
            v___x_1832_,
            v___x_2120_,
            v___x_1789_,
        );
        v___x_2125_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2123_,
            v___x_1834_,
            v___x_2124_,
        );
        v___x_2126_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2125_);
        v___x_2127_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2126_);
        v___x_2128_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2117_,
            v___x_2127_,
            v___x_2080_,
        );
        lean_inc_n(v___x_2113_, 4);
        v___x_2129_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2113_, v___x_2128_);
        v___x_2130_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246);
        v___x_2131_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247;
        v___x_2132_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2132_, 0, v___x_1720_);
        lean_ctor_set(v___x_2132_, 1, v___x_2130_);
        lean_ctor_set(v___x_2132_, 2, v___x_2131_);
        lean_ctor_set(v___x_2132_, 3, v___x_1739_);
        v___x_2133_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2132_, v___x_1729_);
        v___x_2134_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249;
        v___x_2135_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250;
        v___x_2136_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2136_, 0, v___x_1720_);
        lean_ctor_set(v___x_2136_, 1, v___x_2135_);
        lean_inc_ref(v___x_2136_);
        v___x_2137_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2134_,
            v___x_1763_,
            v___x_2136_,
            v___x_1766_,
        );
        v___x_2138_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2137_,
            v___x_1871_,
        );
        v___x_2139_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2138_,
            v___x_2025_,
            v___x_2059_,
        );
        v___x_2140_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2134_,
            v___x_1832_,
            v___x_2136_,
            v___x_1789_,
        );
        v___x_2141_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2139_,
            v___x_1834_,
            v___x_2140_,
        );
        v___x_2142_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2141_);
        v___x_2143_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2142_);
        v___x_2144_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2133_,
            v___x_2143_,
            v___x_2080_,
        );
        v___x_2145_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2113_, v___x_2144_);
        v___x_2146_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252);
        v___x_2147_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253;
        v___x_2148_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2148_, 0, v___x_1720_);
        lean_ctor_set(v___x_2148_, 1, v___x_2146_);
        lean_ctor_set(v___x_2148_, 2, v___x_2147_);
        lean_ctor_set(v___x_2148_, 3, v___x_1739_);
        v___x_2149_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2148_, v___x_1729_);
        v___x_2150_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255;
        v___x_2151_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256;
        v___x_2152_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2152_, 0, v___x_1720_);
        lean_ctor_set(v___x_2152_, 1, v___x_2151_);
        lean_inc_ref(v___x_2152_);
        v___x_2153_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2150_,
            v___x_1763_,
            v___x_2152_,
            v___x_1766_,
        );
        v___x_2154_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2153_,
            v___x_1871_,
        );
        v___x_2155_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2154_,
            v___x_2025_,
            v___x_2059_,
        );
        v___x_2156_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2150_,
            v___x_1832_,
            v___x_2152_,
            v___x_1789_,
        );
        v___x_2157_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2155_,
            v___x_1834_,
            v___x_2156_,
        );
        v___x_2158_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2157_);
        v___x_2159_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2158_);
        v___x_2160_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2149_,
            v___x_2159_,
            v___x_2080_,
        );
        v___x_2161_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2113_, v___x_2160_);
        v___x_2162_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258);
        v___x_2163_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259;
        v___x_2164_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2164_, 0, v___x_1720_);
        lean_ctor_set(v___x_2164_, 1, v___x_2162_);
        lean_ctor_set(v___x_2164_, 2, v___x_2163_);
        lean_ctor_set(v___x_2164_, 3, v___x_1739_);
        v___x_2165_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2164_, v___x_1729_);
        v___x_2166_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261;
        v___x_2167_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262;
        v___x_2168_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2168_, 0, v___x_1720_);
        lean_ctor_set(v___x_2168_, 1, v___x_2167_);
        v___x_2169_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2166_,
            v___x_1763_,
            v___x_2168_,
            v___x_1766_,
        );
        v___x_2170_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2169_,
            v___x_1871_,
        );
        v___x_2171_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2170_,
            v___x_2025_,
            v___x_2059_,
        );
        v___x_2172_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264);
        v___x_2173_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266;
        v___x_2174_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2174_, 0, v___x_1720_);
        lean_ctor_set(v___x_2174_, 1, v___x_2172_);
        lean_ctor_set(v___x_2174_, 2, v___x_2173_);
        lean_ctor_set(v___x_2174_, 3, v___x_1739_);
        v___x_2175_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2174_, v___x_1790_);
        v___x_2176_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2171_,
            v___x_1834_,
            v___x_2175_,
        );
        v___x_2177_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2176_);
        v___x_2178_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2177_);
        v___x_2179_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2165_,
            v___x_2178_,
            v___x_2080_,
        );
        v___x_2180_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2113_, v___x_2179_);
        v___x_2181_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268);
        v___x_2182_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269;
        v___x_2183_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2183_, 0, v___x_1720_);
        lean_ctor_set(v___x_2183_, 1, v___x_2181_);
        lean_ctor_set(v___x_2183_, 2, v___x_2182_);
        lean_ctor_set(v___x_2183_, 3, v___x_1739_);
        v___x_2184_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1752_, v___x_2183_, v___x_1729_);
        v___x_2185_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271;
        v___x_2186_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272;
        v___x_2187_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2187_, 0, v___x_1720_);
        lean_ctor_set(v___x_2187_, 1, v___x_2186_);
        v___x_2188_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2185_,
            v___x_1763_,
            v___x_2187_,
            v___x_1766_,
        );
        v___x_2189_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1848_,
            v___x_1857_,
            v___x_2188_,
            v___x_1871_,
        );
        v___x_2190_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_2020_,
            v___x_2189_,
            v___x_2025_,
            v___x_2059_,
        );
        v___x_2191_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_once), _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274);
        v___x_2192_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276;
        v___x_2193_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2193_, 0, v___x_1720_);
        lean_ctor_set(v___x_2193_, 1, v___x_2191_);
        lean_ctor_set(v___x_2193_, 2, v___x_2192_);
        lean_ctor_set(v___x_2193_, 3, v___x_1739_);
        v___x_2194_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1783_, v___x_2193_, v___x_1790_);
        v___x_2195_ = l_Lean_Syntax_node3(
            v___x_1720_,
            v___x_1829_,
            v___x_2190_,
            v___x_1834_,
            v___x_2194_,
        );
        v___x_2196_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1775_, v___x_1769_, v___x_2195_);
        v___x_2197_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1757_, v___x_1774_, v___x_2196_);
        v___x_2198_ = l_Lean_Syntax_node4(
            v___x_1720_,
            v___x_1750_,
            v___x_1751_,
            v___x_2184_,
            v___x_2197_,
            v___x_2080_,
        );
        v___x_2199_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1726_, v___x_2113_, v___x_2198_);
        v___x_2200_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277;
        v___x_2201_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278;
        v___x_2202_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2202_, 0, v___x_1720_);
        lean_ctor_set(v___x_2202_, 1, v___x_2200_);
        v___x_2203_ = l_Lean_Syntax_node2(v___x_1720_, v___x_1721_, v___x_1716_, v___x_1729_);
        v___x_2204_ = l_Lean_Syntax_node2(v___x_1720_, v___x_2201_, v___x_2202_, v___x_2203_);
        v___x_2205_ = lean_unsigned_to_nat(17);
        v___x_2206_ = lean_mk_empty_array_with_capacity(v___x_2205_);
        v___x_2207_ = lean_array_push(v___x_2206_, v___x_1725_);
        v___x_2208_ = lean_array_push(v___x_2207_, v___x_1806_);
        v___x_2209_ = lean_array_push(v___x_2208_, v___x_1823_);
        v___x_2210_ = lean_array_push(v___x_2209_, v___x_1879_);
        v___x_2211_ = lean_array_push(v___x_2210_, v___x_1954_);
        v___x_2212_ = lean_array_push(v___x_2211_, v___x_1967_);
        v___x_2213_ = lean_array_push(v___x_2212_, v___x_1998_);
        v___x_2214_ = lean_array_push(v___x_2213_, v___x_2011_);
        v___x_2215_ = lean_array_push(v___x_2214_, v___x_2035_);
        v___x_2216_ = lean_array_push(v___x_2215_, v___x_2082_);
        v___x_2217_ = lean_array_push(v___x_2216_, v___x_2107_);
        v___x_2218_ = lean_array_push(v___x_2217_, v___x_2129_);
        v___x_2219_ = lean_array_push(v___x_2218_, v___x_2145_);
        v___x_2220_ = lean_array_push(v___x_2219_, v___x_2161_);
        v___x_2221_ = lean_array_push(v___x_2220_, v___x_2180_);
        v___x_2222_ = lean_array_push(v___x_2221_, v___x_2199_);
        v___x_2223_ = lean_array_push(v___x_2222_, v___x_2204_);
        v___x_2224_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2224_, 0, v___x_1720_);
        lean_ctor_set(v___x_2224_, 1, v___x_1721_);
        lean_ctor_set(v___x_2224_, 2, v___x_2223_);
        v___x_2225_ = l_Lean_Syntax_getArgs(v___x_2224_);
        lean_dec_ref_known(v___x_2224_, 3);
        v___x_2226_ = lean_box(2);
        v___x_2227_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2227_, 0, v___x_2226_);
        lean_ctor_set(v___x_2227_, 1, v___x_1721_);
        lean_ctor_set(v___x_2227_, 2, v___x_2225_);
        v___x_2228_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2228_, 0, v___x_2227_);
        lean_ctor_set(v___x_2228_, 1, v_a_1709_);
        return v___x_2228_;
    }
}
pub unsafe fn l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___boxed(
    mut v_x_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2232_: *mut LeanObject = core::ptr::null_mut();
    v_res_2232_ =
        l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(
            v_x_2229_, v_a_2230_, v_a_2231_,
        );
    lean_dec_ref(v_a_2230_);
    return v_res_2232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_SInt_Lemmas(builtin);
}
