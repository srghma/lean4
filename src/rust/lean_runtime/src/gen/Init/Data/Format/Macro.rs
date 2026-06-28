// Lean compiler output
// Module: Init.Data.Format.Macro
// Imports: Init.Meta Init.Notation
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_expandInterpolatedStr;
use crate::r#gen::Init::Meta::{initialize_Init_Meta, meta_initialize_Init_Meta};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Std_termF_x21___00__closed__0_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Std_termF_x21___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__0_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 70, 33, 95, 0],
};
static mut l_Std_termF_x21___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__1_value) as *mut LeanObject;
static l_Std_termF_x21___00__closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__0_value) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l_Std_termF_x21___00__closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__1_value) as *mut LeanObject,
        16360410401156225260 as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__2_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__3_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_termF_x21___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__3_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__4_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__5_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [102, 33, 0],
};
static mut l_Std_termF_x21___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__5_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Std_termF_x21___00__closed__5_value) as *mut LeanObject],
};
static mut l_Std_termF_x21___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__6_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__7_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_Std_termF_x21___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__7_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__7_value) as *mut LeanObject,
        18163029821153688220 as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__8_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__9_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_termF_x21___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__9_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__9_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__10_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__10_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__11_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__12_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__13_value) as *mut LeanObject;
pub static l_Std_termF_x21___00__closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__2_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_termF_x21___00__closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Std_termF_x21___00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__14_value) as *mut LeanObject;
pub static mut l_Std_termF_x21__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_termF_x21___00__closed__14_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 111, 114, 109, 97, 116, 0]};
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value) as *mut LeanObject,18438390214131365702 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_termF_x21___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value) as *mut LeanObject,12875137807382502537 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [83, 116, 100, 46, 102, 111, 114, 109, 97, 116, 0]};
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8_value) as *mut LeanObject;
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 111, 114, 109, 97, 116, 0]};
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_termF_x21___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value) as *mut LeanObject,16492119629179343846 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 70, 111, 114, 109, 97, 116, 0]};
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value) as *mut LeanObject;
static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_termF_x21___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value) as *mut LeanObject,7757968602677615422 as *mut LeanObject] };
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value) as *mut LeanObject,8725156003221708992 as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value) as *mut LeanObject;
pub static l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15_value) as *mut LeanObject;
pub unsafe fn _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1()
-> *mut LeanObject {
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    v___x_150_ =
        l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0;
    v___x_151_ = l_String_toRawSubstring_x27(v___x_150_);
    return v___x_151_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9()
-> *mut LeanObject {
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___x_169_ =
        l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8;
    v___x_170_ = l_String_toRawSubstring_x27(v___x_169_);
    return v___x_170_;
}
pub unsafe fn l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1(
    mut v_x_186_: *mut LeanObject,
    mut v_a_187_: *mut LeanObject,
    mut v_a_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: u8 = 0;
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interpStr_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: u8 = 0;
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_215_: u8 = 0;
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_a_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_224_: u8 = 0;
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_189_ = l_Std_termF_x21___00__closed__2;
                lean_inc(v_x_186_);
                v___x_190_ = l_Lean_Syntax_isOfKind(v_x_186_, v___x_189_);
                if v___x_190_ == 0 {
                    lean_dec(v_x_186_);
                    v___x_191_ = lean_box(1);
                    v___x_192_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_192_, 0, v___x_191_);
                    lean_ctor_set(v___x_192_, 1, v_a_188_);
                    return v___x_192_;
                } else {
                    v_quotContext_193_ = lean_ctor_get(v_a_187_, 1);
                    v_currMacroScope_194_ = lean_ctor_get(v_a_187_, 2);
                    v_ref_195_ = lean_ctor_get(v_a_187_, 5);
                    v___x_196_ = lean_unsigned_to_nat(1);
                    v_interpStr_197_ = l_Lean_Syntax_getArg(v_x_186_, v___x_196_);
                    lean_dec(v_x_186_);
                    v___x_198_ = 0;
                    v___x_199_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_198_);
                    v___x_200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1_once), _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1);
                    v___x_201_ = l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2;
                    lean_inc_n(v_currMacroScope_194_, 2);
                    lean_inc_n(v_quotContext_193_, 2);
                    v___x_202_ =
                        l_Lean_addMacroScope(v_quotContext_193_, v___x_201_, v_currMacroScope_194_);
                    v___x_203_ = l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7;
                    lean_inc(v___x_199_);
                    v___x_204_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_204_, 0, v___x_199_);
                    lean_ctor_set(v___x_204_, 1, v___x_200_);
                    lean_ctor_set(v___x_204_, 2, v___x_202_);
                    lean_ctor_set(v___x_204_, 3, v___x_203_);
                    v___x_205_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9_once), _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9);
                    v___x_206_ = l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11;
                    v___x_207_ =
                        l_Lean_addMacroScope(v_quotContext_193_, v___x_206_, v_currMacroScope_194_);
                    v___x_208_ = l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15;
                    v___x_209_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_209_, 0, v___x_199_);
                    lean_ctor_set(v___x_209_, 1, v___x_205_);
                    lean_ctor_set(v___x_209_, 2, v___x_207_);
                    lean_ctor_set(v___x_209_, 3, v___x_208_);
                    lean_inc_ref(v___x_209_);
                    v___x_210_ = l_Lean_TSyntax_expandInterpolatedStr(
                        v_interpStr_197_,
                        v___x_204_,
                        v___x_209_,
                        v___x_209_,
                        v_a_187_,
                        v_a_188_,
                    );
                    lean_dec(v_interpStr_197_);
                    if lean_obj_tag(v___x_210_) == 0 {
                        v_a_211_ = lean_ctor_get(v___x_210_, 0);
                        v_a_212_ = lean_ctor_get(v___x_210_, 1);
                        v_isSharedCheck_219_ = (!lean_is_exclusive(v___x_210_)) as u8;
                        if v_isSharedCheck_219_ == 0 {
                            v___x_214_ = v___x_210_;
                            v_isShared_215_ = v_isSharedCheck_219_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_212_);
                            lean_inc(v_a_211_);
                            lean_dec(v___x_210_);
                            v___x_214_ = lean_box(0);
                            v_isShared_215_ = v_isSharedCheck_219_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_220_ = lean_ctor_get(v___x_210_, 0);
                        v_a_221_ = lean_ctor_get(v___x_210_, 1);
                        v_isSharedCheck_228_ = (!lean_is_exclusive(v___x_210_)) as u8;
                        if v_isSharedCheck_228_ == 0 {
                            v___x_223_ = v___x_210_;
                            v_isShared_224_ = v_isSharedCheck_228_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_221_);
                            lean_inc(v_a_220_);
                            lean_dec(v___x_210_);
                            v___x_223_ = lean_box(0);
                            v_isShared_224_ = v_isSharedCheck_228_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_215_ == 0 {
                    v___x_217_ = v___x_214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_211_);
                    lean_ctor_set(v_reuseFailAlloc_218_, 1, v_a_212_);
                    v___x_217_ = v_reuseFailAlloc_218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_217_;
            }
            3 => {
                if v_isShared_224_ == 0 {
                    v___x_226_ = v___x_223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
                    lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_221_);
                    v___x_226_ = v_reuseFailAlloc_227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___boxed(
    mut v_x_229_: *mut LeanObject,
    mut v_a_230_: *mut LeanObject,
    mut v_a_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_232_: *mut LeanObject = core::ptr::null_mut();
    v_res_232_ = l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1(
        v_x_229_, v_a_230_, v_a_231_,
    );
    lean_dec_ref(v_a_230_);
    return v_res_232_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Macro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Macro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Macro(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Format_Macro(builtin);
}
