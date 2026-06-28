// Lean compiler output
// Module: Init.Internal.Order.Basic
// Imports: Init.System.IO Init.Control.Except Init.Control.StateRef Init.Control.Option Init.System.ST Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
use crate::r#gen::Init::Control::StateRef::{
    initialize_Init_Control_StateRef, runtime_initialize_Init_Control_StateRef,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::ST::{
    initialize_Init_System_ST, runtime_initialize_Init_System_ST,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Order_term___u2291___00__closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Order_term___u2291___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__1_value: LeanStringObject<6> =
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
        m_data: [79, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Order_term___u2291___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 7,
        m_data: [116, 101, 114, 109, 95, 226, 138, 145, 95, 0],
    };
static mut l_Lean_Order_term___u2291___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__2_value) as *mut LeanObject;
static l_Lean_Order_term___u2291___00__closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Order_term___u2291___00__closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Order_term___u2291___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__2_value) as *mut LeanObject,
        12429467445819385663 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__4_value: LeanStringObject<8> =
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
static mut l_Lean_Order_term___u2291___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__4_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__5_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 145, 32, 0],
    };
static mut l_Lean_Order_term___u2291___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__6_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__7_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Order_term___u2291___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__8_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__9_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__9_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__10_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__11_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2291___00__closed__12_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__3_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2291___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Order_term___u2291__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__12_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value) as *mut LeanObject;
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__2_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 97, 114, 116, 105, 97, 108, 79, 114, 100, 101, 114, 46, 114, 101, 108, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4_value) as *mut LeanObject;
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 97, 114, 116, 105, 97, 108, 79, 114, 100, 101, 114, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 108, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value) as *mut LeanObject;
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value) as *mut LeanObject,5519389714833130543 as *mut LeanObject] };
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value) as *mut LeanObject,12524182874559658317 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8_value) as *mut LeanObject;
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__1_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__6_value) as *mut LeanObject,12780732901949572019 as *mut LeanObject] };
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__7_value) as *mut LeanObject,9034587416841137705 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a5___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 5,
    m_data: [116, 101, 114, 109, 226, 138, 165, 0],
};
static mut l_Lean_Order_term_u22a5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__0_value) as *mut LeanObject;
static l_Lean_Order_term_u22a5___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Order_term_u22a5___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Order_term_u22a5___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__0_value) as *mut LeanObject,
        14079511657030373096 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term_u22a5___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a5___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 138, 165, 0],
};
static mut l_Lean_Order_term_u22a5___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__2_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a5___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Order_term_u22a5___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a5___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term_u22a5___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Order_term_u22a5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a5___closed__4_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 111, 116, 0]};
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value) as *mut LeanObject,17987950242264974901 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2_value) as *mut LeanObject;
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u2291___00__closed__1_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0_value) as *mut LeanObject,9887338369843671897 as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Order_ImplicationOrder_instOrder: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Order_ImplicationOrder_instCompleteLattice: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Order_ReverseImplicationOrder_instOrder: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Order_ReverseImplicationOrder_instCompleteLattice: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5()
-> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__4;
    v___x_399_ = l_String_toRawSubstring_x27(v___x_398_);
    return v___x_399_;
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(
    mut v_x_419_: *mut LeanObject,
    mut v_a_420_: *mut LeanObject,
    mut v_a_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    v___x_422_ = l_Lean_Order_term___u2291___00__closed__3;
    lean_inc(v_x_419_);
    v___x_423_ = l_Lean_Syntax_isOfKind(v_x_419_, v___x_422_);
    if v___x_423_ == 0 {
        let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_419_);
        v___x_424_ = lean_box(1);
        v___x_425_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_425_, 0, v___x_424_);
        lean_ctor_set(v___x_425_, 1, v_a_421_);
        return v___x_425_;
    } else {
        let mut v_quotContext_426_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_433_: u8 = 0;
        let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_426_ = lean_ctor_get(v_a_420_, 1);
        v_currMacroScope_427_ = lean_ctor_get(v_a_420_, 2);
        v_ref_428_ = lean_ctor_get(v_a_420_, 5);
        v___x_429_ = lean_unsigned_to_nat(0);
        v___x_430_ = l_Lean_Syntax_getArg(v_x_419_, v___x_429_);
        v___x_431_ = lean_unsigned_to_nat(2);
        v___x_432_ = l_Lean_Syntax_getArg(v_x_419_, v___x_431_);
        lean_dec(v_x_419_);
        v___x_433_ = 0;
        v___x_434_ = l_Lean_SourceInfo_fromRef(v_ref_428_, v___x_433_);
        v___x_435_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3;
        v___x_436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5), core::ptr::addr_of_mut!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5_once), _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__5);
        v___x_437_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__8;
        lean_inc(v_currMacroScope_427_);
        lean_inc(v_quotContext_426_);
        v___x_438_ = l_Lean_addMacroScope(v_quotContext_426_, v___x_437_, v_currMacroScope_427_);
        v___x_439_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__11;
        lean_inc_n(v___x_434_, 2);
        v___x_440_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_440_, 0, v___x_434_);
        lean_ctor_set(v___x_440_, 1, v___x_436_);
        lean_ctor_set(v___x_440_, 2, v___x_438_);
        lean_ctor_set(v___x_440_, 3, v___x_439_);
        v___x_441_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__13;
        v___x_442_ = l_Lean_Syntax_node2(v___x_434_, v___x_441_, v___x_430_, v___x_432_);
        v___x_443_ = l_Lean_Syntax_node2(v___x_434_, v___x_435_, v___x_440_, v___x_442_);
        v___x_444_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_444_, 0, v___x_443_);
        lean_ctor_set(v___x_444_, 1, v_a_421_);
        return v___x_444_;
    }
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___boxed(
    mut v_x_445_: *mut LeanObject,
    mut v_a_446_: *mut LeanObject,
    mut v_a_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_448_: *mut LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1(v_x_445_, v_a_446_, v_a_447_);
    lean_dec_ref(v_a_446_);
    return v_res_448_;
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(
    mut v_x_452_: *mut LeanObject,
    mut v_a_453_: *mut LeanObject,
    mut v_a_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    v___x_455_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term___u2291____1___closed__3;
    lean_inc(v_x_452_);
    v___x_456_ = l_Lean_Syntax_isOfKind(v_x_452_, v___x_455_);
    if v___x_456_ == 0 {
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_452_);
        v___x_457_ = lean_box(0);
        v___x_458_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_458_, 0, v___x_457_);
        lean_ctor_set(v___x_458_, 1, v_a_454_);
        return v___x_458_;
    } else {
        let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_462_: u8 = 0;
        v___x_459_ = lean_unsigned_to_nat(0);
        v___x_460_ = l_Lean_Syntax_getArg(v_x_452_, v___x_459_);
        v___x_461_ = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1;
        lean_inc(v___x_460_);
        v___x_462_ = l_Lean_Syntax_isOfKind(v___x_460_, v___x_461_);
        if v___x_462_ == 0 {
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_460_);
            lean_dec(v_x_452_);
            v___x_463_ = lean_box(0);
            v___x_464_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_464_, 0, v___x_463_);
            lean_ctor_set(v___x_464_, 1, v_a_454_);
            return v___x_464_;
        } else {
            let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_468_: u8 = 0;
            v___x_465_ = lean_unsigned_to_nat(1);
            v___x_466_ = l_Lean_Syntax_getArg(v_x_452_, v___x_465_);
            lean_dec(v_x_452_);
            v___x_467_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_466_);
            v___x_468_ = l_Lean_Syntax_matchesNull(v___x_466_, v___x_467_);
            if v___x_468_ == 0 {
                let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_466_);
                lean_dec(v___x_460_);
                v___x_469_ = lean_box(0);
                v___x_470_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_470_, 0, v___x_469_);
                lean_ctor_set(v___x_470_, 1, v_a_454_);
                return v___x_470_;
            } else {
                let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_473_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_474_: u8 = 0;
                let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
                v___x_471_ = l_Lean_Syntax_getArg(v___x_466_, v___x_459_);
                v___x_472_ = l_Lean_Syntax_getArg(v___x_466_, v___x_465_);
                lean_dec(v___x_466_);
                v_ref_473_ = l_Lean_replaceRef(v___x_460_, v_a_453_);
                lean_dec(v___x_460_);
                v___x_474_ = 0;
                v___x_475_ = l_Lean_SourceInfo_fromRef(v_ref_473_, v___x_474_);
                lean_dec(v_ref_473_);
                v___x_476_ = l_Lean_Order_term___u2291___00__closed__3;
                v___x_477_ = l_Lean_Order_term___u2291___00__closed__6;
                lean_inc(v___x_475_);
                v___x_478_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_478_, 0, v___x_475_);
                lean_ctor_set(v___x_478_, 1, v___x_477_);
                v___x_479_ =
                    l_Lean_Syntax_node3(v___x_475_, v___x_476_, v___x_471_, v___x_478_, v___x_472_);
                v___x_480_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_480_, 0, v___x_479_);
                lean_ctor_set(v___x_480_, 1, v_a_454_);
                return v___x_480_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___boxed(
    mut v_x_481_: *mut LeanObject,
    mut v_a_482_: *mut LeanObject,
    mut v_a_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1(v_x_481_, v_a_482_, v_a_483_);
    lean_dec(v_a_482_);
    return v_res_484_;
}
pub unsafe fn _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1()
-> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__0;
    v___x_500_ = l_String_toRawSubstring_x27(v___x_499_);
    return v___x_500_;
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(
    mut v_x_513_: *mut LeanObject,
    mut v_a_514_: *mut LeanObject,
    mut v_a_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: u8 = 0;
    v___x_516_ = l_Lean_Order_term_u22a5___closed__1;
    v___x_517_ = l_Lean_Syntax_isOfKind(v_x_513_, v___x_516_);
    if v___x_517_ == 0 {
        let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        v___x_518_ = lean_box(1);
        v___x_519_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_519_, 0, v___x_518_);
        lean_ctor_set(v___x_519_, 1, v_a_515_);
        return v___x_519_;
    } else {
        let mut v_quotContext_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_521_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_523_: u8 = 0;
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_520_ = lean_ctor_get(v_a_514_, 1);
        v_currMacroScope_521_ = lean_ctor_get(v_a_514_, 2);
        v_ref_522_ = lean_ctor_get(v_a_514_, 5);
        v___x_523_ = 0;
        v___x_524_ = l_Lean_SourceInfo_fromRef(v_ref_522_, v___x_523_);
        v___x_525_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1_once), _init_l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__1);
        v___x_526_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__2;
        lean_inc(v_currMacroScope_521_);
        lean_inc(v_quotContext_520_);
        v___x_527_ = l_Lean_addMacroScope(v_quotContext_520_, v___x_526_, v_currMacroScope_521_);
        v___x_528_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___closed__5;
        v___x_529_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_529_, 0, v___x_524_);
        lean_ctor_set(v___x_529_, 1, v___x_525_);
        lean_ctor_set(v___x_529_, 2, v___x_527_);
        lean_ctor_set(v___x_529_, 3, v___x_528_);
        v___x_530_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_530_, 0, v___x_529_);
        lean_ctor_set(v___x_530_, 1, v_a_515_);
        return v___x_530_;
    }
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1___boxed(
    mut v_x_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_534_: *mut LeanObject = core::ptr::null_mut();
    v_res_534_ = l_Lean_Order___aux__Init__Internal__Order__Basic______macroRules__Lean__Order__term_u22a5__1(v_x_531_, v_a_532_, v_a_533_);
    lean_dec_ref(v_a_532_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(
    mut v_x_535_: *mut LeanObject,
    mut v_a_536_: *mut LeanObject,
    mut v_a_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: u8 = 0;
    v___x_538_ = l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__PartialOrder__rel__1___closed__1;
    lean_inc(v_x_535_);
    v___x_539_ = l_Lean_Syntax_isOfKind(v_x_535_, v___x_538_);
    if v___x_539_ == 0 {
        let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_535_);
        v___x_540_ = lean_box(0);
        v___x_541_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_541_, 0, v___x_540_);
        lean_ctor_set(v___x_541_, 1, v_a_537_);
        return v___x_541_;
    } else {
        let mut v_ref_542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_543_: u8 = 0;
        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
        v_ref_542_ = l_Lean_replaceRef(v_x_535_, v_a_536_);
        lean_dec(v_x_535_);
        v___x_543_ = 0;
        v___x_544_ = l_Lean_SourceInfo_fromRef(v_ref_542_, v___x_543_);
        lean_dec(v_ref_542_);
        v___x_545_ = l_Lean_Order_term_u22a5___closed__1;
        v___x_546_ = l_Lean_Order_term_u22a5___closed__2;
        lean_inc(v___x_544_);
        v___x_547_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_547_, 0, v___x_544_);
        lean_ctor_set(v___x_547_, 1, v___x_546_);
        v___x_548_ = l_Lean_Syntax_node1(v___x_544_, v___x_545_, v___x_547_);
        v___x_549_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_549_, 0, v___x_548_);
        lean_ctor_set(v___x_549_, 1, v_a_537_);
        return v___x_549_;
    }
}
pub unsafe fn l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1___boxed(
    mut v_x_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_553_: *mut LeanObject = core::ptr::null_mut();
    v_res_553_ =
        l_Lean_Order___aux__Init__Internal__Order__Basic______unexpand__Lean__Order__bot__1(
            v_x_550_, v_a_551_, v_a_552_,
        );
    lean_dec(v_a_551_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Order_instOrderPi(
    mut v_00_u03b1_554_: *mut LeanObject,
    mut v_00_u03b2_555_: *mut LeanObject,
    mut v_inst_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_box(0);
    return v___x_557_;
}
pub unsafe fn l_Lean_Order_instOrderPi___boxed(
    mut v_00_u03b1_558_: *mut LeanObject,
    mut v_00_u03b2_559_: *mut LeanObject,
    mut v_inst_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_561_: *mut LeanObject = core::ptr::null_mut();
    v_res_561_ = l_Lean_Order_instOrderPi(v_00_u03b1_558_, v_00_u03b2_559_, v_inst_560_);
    lean_dec_ref(v_inst_560_);
    return v_res_561_;
}
pub unsafe fn l_Lean_Order_instCCPOPi(
    mut v_00_u03b1_562_: *mut LeanObject,
    mut v_00_u03b2_563_: *mut LeanObject,
    mut v_inst_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = lean_box(0);
    return v___x_565_;
}
pub unsafe fn l_Lean_Order_instCCPOPi___boxed(
    mut v_00_u03b1_566_: *mut LeanObject,
    mut v_00_u03b2_567_: *mut LeanObject,
    mut v_inst_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_569_: *mut LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Lean_Order_instCCPOPi(v_00_u03b1_566_, v_00_u03b2_567_, v_inst_568_);
    lean_dec_ref(v_inst_568_);
    return v_res_569_;
}
pub unsafe fn l_Lean_Order_instCompleteLatticePi(
    mut v_00_u03b1_570_: *mut LeanObject,
    mut v_00_u03b2_571_: *mut LeanObject,
    mut v_inst_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = lean_box(0);
    return v___x_573_;
}
pub unsafe fn l_Lean_Order_instCompleteLatticePi___boxed(
    mut v_00_u03b1_574_: *mut LeanObject,
    mut v_00_u03b2_575_: *mut LeanObject,
    mut v_inst_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_577_: *mut LeanObject = core::ptr::null_mut();
    v_res_577_ = l_Lean_Order_instCompleteLatticePi(v_00_u03b1_574_, v_00_u03b2_575_, v_inst_576_);
    lean_dec_ref(v_inst_576_);
    return v_res_577_;
}
pub unsafe fn l_Lean_Order_instPartialOrderPProd(
    mut v_00_u03b1_578_: *mut LeanObject,
    mut v_00_u03b2_579_: *mut LeanObject,
    mut v_inst_580_: *mut LeanObject,
    mut v_inst_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_box(0);
    return v___x_582_;
}
pub unsafe fn l_Lean_Order_instCCPOPProd(
    mut v_00_u03b1_583_: *mut LeanObject,
    mut v_00_u03b2_584_: *mut LeanObject,
    mut v_inst_585_: *mut LeanObject,
    mut v_inst_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_587_ = lean_box(0);
    return v___x_587_;
}
pub unsafe fn l_Lean_Order_instCompleteLatticePProd(
    mut v_00_u03b1_588_: *mut LeanObject,
    mut v_00_u03b2_589_: *mut LeanObject,
    mut v_inst_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_box(0);
    return v___x_592_;
}
pub unsafe fn l_Lean_Order_FlatOrder_instOrder(
    mut v_00_u03b1_593_: *mut LeanObject,
    mut v_b_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = lean_box(0);
    return v___x_595_;
}
pub unsafe fn l_Lean_Order_FlatOrder_instOrder___boxed(
    mut v_00_u03b1_596_: *mut LeanObject,
    mut v_b_597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_598_: *mut LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lean_Order_FlatOrder_instOrder(v_00_u03b1_596_, v_b_597_);
    lean_dec(v_b_597_);
    return v_res_598_;
}
pub unsafe fn l_Lean_Order_FlatOrder_instCCPO(
    mut v_00_u03b1_599_: *mut LeanObject,
    mut v_b_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = lean_box(0);
    return v___x_601_;
}
pub unsafe fn l_Lean_Order_FlatOrder_instCCPO___boxed(
    mut v_00_u03b1_602_: *mut LeanObject,
    mut v_b_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_604_: *mut LeanObject = core::ptr::null_mut();
    v_res_604_ = l_Lean_Order_FlatOrder_instCCPO(v_00_u03b1_602_, v_b_603_);
    lean_dec(v_b_603_);
    return v_res_604_;
}
pub unsafe fn l_Lean_Order_instPartialOrderOption(
    mut v_00_u03b1_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    v___x_606_ = lean_box(0);
    return v___x_606_;
}
pub unsafe fn l_Lean_Order_instCCPOOption(mut v_00_u03b1_607_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_box(0);
    return v___x_608_;
}
pub unsafe fn l_Lean_Order_instPartialOrderExceptT___redArg(
    mut v_inst_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ = lean_apply_1(v_inst_609_, lean_box(0));
    return v___x_610_;
}
pub unsafe fn l_Lean_Order_instPartialOrderExceptT(
    mut v_m_611_: *mut LeanObject,
    mut v_00_u03b5_612_: *mut LeanObject,
    mut v_00_u03b1_613_: *mut LeanObject,
    mut v_inst_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = lean_apply_1(v_inst_614_, lean_box(0));
    return v___x_615_;
}
pub unsafe fn l_Lean_Order_instCCPOExceptT___redArg(
    mut v_inst_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = lean_apply_1(v_inst_616_, lean_box(0));
    return v___x_617_;
}
pub unsafe fn l_Lean_Order_instCCPOExceptT(
    mut v_m_618_: *mut LeanObject,
    mut v_00_u03b5_619_: *mut LeanObject,
    mut v_00_u03b1_620_: *mut LeanObject,
    mut v_inst_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = lean_apply_1(v_inst_621_, lean_box(0));
    return v___x_622_;
}
pub unsafe fn l_Lean_Order_instPartialOrderOptionT___redArg(
    mut v_inst_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = lean_apply_1(v_inst_623_, lean_box(0));
    return v___x_624_;
}
pub unsafe fn l_Lean_Order_instPartialOrderOptionT(
    mut v_m_625_: *mut LeanObject,
    mut v_00_u03b1_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v___x_628_ = lean_apply_1(v_inst_627_, lean_box(0));
    return v___x_628_;
}
pub unsafe fn l_Lean_Order_instCCPOOptionT___redArg(
    mut v_inst_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = lean_apply_1(v_inst_629_, lean_box(0));
    return v___x_630_;
}
pub unsafe fn l_Lean_Order_instCCPOOptionT(
    mut v_m_631_: *mut LeanObject,
    mut v_00_u03b1_632_: *mut LeanObject,
    mut v_inst_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    v___x_634_ = lean_apply_1(v_inst_633_, lean_box(0));
    return v___x_634_;
}
pub unsafe fn l_Lean_Order_instPartialOrderReaderT(
    mut v_m_635_: *mut LeanObject,
    mut v_00_u03c1_636_: *mut LeanObject,
    mut v_00_u03b1_637_: *mut LeanObject,
    mut v_inst_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = lean_box(0);
    return v___x_639_;
}
pub unsafe fn l_Lean_Order_instCCPOReaderT(
    mut v_m_640_: *mut LeanObject,
    mut v_00_u03c1_641_: *mut LeanObject,
    mut v_00_u03b1_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = lean_box(0);
    return v___x_644_;
}
pub unsafe fn l_Lean_Order_instPartialOrderStateRefT_x27(
    mut v_m_645_: *mut LeanObject,
    mut v_00_u03c9_646_: *mut LeanObject,
    mut v_00_u03c3_647_: *mut LeanObject,
    mut v_00_u03b1_648_: *mut LeanObject,
    mut v_inst_649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    v___x_650_ = lean_box(0);
    return v___x_650_;
}
pub unsafe fn l_Lean_Order_instCCPOStateRefT_x27(
    mut v_m_651_: *mut LeanObject,
    mut v_00_u03c9_652_: *mut LeanObject,
    mut v_00_u03c3_653_: *mut LeanObject,
    mut v_00_u03b1_654_: *mut LeanObject,
    mut v_inst_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = lean_box(0);
    return v___x_656_;
}
pub unsafe fn l_Lean_Order_instPartialOrderStateT(
    mut v_m_657_: *mut LeanObject,
    mut v_00_u03c3_658_: *mut LeanObject,
    mut v_00_u03b1_659_: *mut LeanObject,
    mut v_inst_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_661_ = lean_box(0);
    return v___x_661_;
}
pub unsafe fn l_Lean_Order_instPartialOrderStateT___boxed(
    mut v_m_662_: *mut LeanObject,
    mut v_00_u03c3_663_: *mut LeanObject,
    mut v_00_u03b1_664_: *mut LeanObject,
    mut v_inst_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_Order_instPartialOrderStateT(
        v_m_662_,
        v_00_u03c3_663_,
        v_00_u03b1_664_,
        v_inst_665_,
    );
    lean_dec_ref(v_inst_665_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Order_instCCPOStateT(
    mut v_m_667_: *mut LeanObject,
    mut v_00_u03c3_668_: *mut LeanObject,
    mut v_00_u03b1_669_: *mut LeanObject,
    mut v_inst_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = lean_box(0);
    return v___x_671_;
}
pub unsafe fn l_Lean_Order_instCCPOStateT___boxed(
    mut v_m_672_: *mut LeanObject,
    mut v_00_u03c3_673_: *mut LeanObject,
    mut v_00_u03b1_674_: *mut LeanObject,
    mut v_inst_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_676_ =
        l_Lean_Order_instCCPOStateT(v_m_672_, v_00_u03c3_673_, v_00_u03b1_674_, v_inst_675_);
    lean_dec_ref(v_inst_675_);
    return v_res_676_;
}
pub unsafe fn l_Lean_Order_instCCPOESTOfNonempty(
    mut v_00_u03b5_677_: *mut LeanObject,
    mut v_00_u03c3_678_: *mut LeanObject,
    mut v_00_u03b1_679_: *mut LeanObject,
    mut v_inst_680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v___x_681_ = lean_box(0);
    return v___x_681_;
}
pub unsafe fn l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter___redArg(
    mut v_x_682_: *mut LeanObject,
    mut v_h__1_683_: *mut LeanObject,
    mut v_h__2_684_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_682_) == 0 {
        let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_684_);
        v_a_685_ = lean_ctor_get(v_x_682_, 0);
        lean_inc(v_a_685_);
        lean_dec_ref_known(v_x_682_, 1);
        v___x_686_ = lean_apply_2(v_h__1_683_, v_a_685_, lean_box(0));
        return v___x_686_;
    } else {
        let mut v_a_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_683_);
        v_a_687_ = lean_ctor_get(v_x_682_, 0);
        lean_inc(v_a_687_);
        lean_dec_ref_known(v_x_682_, 1);
        v___x_688_ = lean_apply_2(v_h__2_684_, v_a_687_, lean_box(0));
        return v___x_688_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_Basic_0__EST_bind_match__1_splitter(
    mut v_00_u03b5_689_: *mut LeanObject,
    mut v_00_u03c3_690_: *mut LeanObject,
    mut v_00_u03b1_691_: *mut LeanObject,
    mut v_motive_692_: *mut LeanObject,
    mut v_x_693_: *mut LeanObject,
    mut v_h__1_694_: *mut LeanObject,
    mut v_h__2_695_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_693_) == 0 {
        let mut v_a_696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_695_);
        v_a_696_ = lean_ctor_get(v_x_693_, 0);
        lean_inc(v_a_696_);
        lean_dec_ref_known(v_x_693_, 1);
        v___x_697_ = lean_apply_2(v_h__1_694_, v_a_696_, lean_box(0));
        return v___x_697_;
    } else {
        let mut v_a_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_694_);
        v_a_698_ = lean_ctor_get(v_x_693_, 0);
        lean_inc(v_a_698_);
        lean_dec_ref_known(v_x_693_, 1);
        v___x_699_ = lean_apply_2(v_h__2_695_, v_a_698_, lean_box(0));
        return v___x_699_;
    }
}
pub unsafe fn l_Lean_Order_instCCPOEIOOfNonempty(
    mut v_00_u03b5_700_: *mut LeanObject,
    mut v_00_u03b1_701_: *mut LeanObject,
    mut v_inst_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_703_ = lean_box(0);
    return v___x_703_;
}
pub unsafe fn l_Lean_Order_instCCPOIO(mut v_00_u03b1_704_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = lean_box(0);
    return v___x_705_;
}
pub unsafe fn _init_l_Lean_Order_ImplicationOrder_instOrder() -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = lean_box(0);
    return v___x_706_;
}
pub unsafe fn _init_l_Lean_Order_ImplicationOrder_instCompleteLattice() -> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ = lean_box(0);
    return v___x_707_;
}
pub unsafe fn _init_l_Lean_Order_ReverseImplicationOrder_instOrder() -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = lean_box(0);
    return v___x_708_;
}
pub unsafe fn _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice() -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_box(0);
    return v___x_709_;
}
pub unsafe fn l_Lean_Order_Example_findF(
    mut v_P_710_: *mut LeanObject,
    mut v_rec_711_: *mut LeanObject,
    mut v_x_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    lean_inc(v_x_712_);
    v___x_713_ = lean_apply_1(v_P_710_, v_x_712_);
    v___x_714_ = (lean_unbox(v___x_713_) as u8);
    if v___x_714_ == 0 {
        let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
        v___x_715_ = lean_unsigned_to_nat(1);
        v___x_716_ = lean_nat_add(v_x_712_, v___x_715_);
        lean_dec(v_x_712_);
        v___x_717_ = lean_apply_1(v_rec_711_, v___x_716_);
        return v___x_717_;
    } else {
        let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_rec_711_);
        v___x_718_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_718_, 0, v_x_712_);
        return v___x_718_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_ST(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Order_ImplicationOrder_instOrder = _init_l_Lean_Order_ImplicationOrder_instOrder();
    lean_mark_persistent(l_Lean_Order_ImplicationOrder_instOrder);
    l_Lean_Order_ImplicationOrder_instCompleteLattice =
        _init_l_Lean_Order_ImplicationOrder_instCompleteLattice();
    lean_mark_persistent(l_Lean_Order_ImplicationOrder_instCompleteLattice);
    l_Lean_Order_ReverseImplicationOrder_instOrder =
        _init_l_Lean_Order_ReverseImplicationOrder_instOrder();
    lean_mark_persistent(l_Lean_Order_ReverseImplicationOrder_instOrder);
    l_Lean_Order_ReverseImplicationOrder_instCompleteLattice =
        _init_l_Lean_Order_ReverseImplicationOrder_instCompleteLattice();
    lean_mark_persistent(l_Lean_Order_ReverseImplicationOrder_instCompleteLattice);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Internal_Order_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Internal_Order_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_StateRef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_ST(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Internal_Order_Basic(builtin);
}
