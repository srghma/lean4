// Lean compiler output
// Module: Std.Do.Triple.Basic
// Imports: Std.Do.WP
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Do::WP::{initialize_Std_Do_WP, runtime_initialize_Std_Do_WP};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Std_Do_triple___closed__0_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Std_Do_triple___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [68, 111, 0],
};
static mut l_Std_Do_triple___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 114, 105, 112, 108, 101, 0],
};
static mut l_Std_Do_triple___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__2_value) as *mut LeanObject;
static l_Std_Do_triple___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Do_triple___closed__0_value) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Std_Do_triple___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__1_value) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
pub static l_Std_Do_triple___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__2_value) as *mut LeanObject,
        13939969460734853986 as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__3_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__4_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_Do_triple___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__4_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Do_triple___closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__6_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 166, 131, 0],
};
static mut l_Std_Do_triple___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Do_triple___closed__6_value) as *mut LeanObject],
};
static mut l_Std_Do_triple___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__7_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_Do_triple___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__8_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Do_triple___closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__9_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__10_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__11_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__12_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 166, 132, 32, 0],
};
static mut l_Std_Do_triple___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__12_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Do_triple___closed__12_value) as *mut LeanObject],
};
static mut l_Std_Do_triple___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__13_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__14_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__15_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__9_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__15_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__16_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__17_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [32, 226, 166, 131, 0],
};
static mut l_Std_Do_triple___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__17_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__18_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Do_triple___closed__17_value) as *mut LeanObject],
};
static mut l_Std_Do_triple___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__18_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__19_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__19_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__19_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__20_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__21_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 166, 132, 0],
};
static mut l_Std_Do_triple___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__21_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__22_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Do_triple___closed__21_value) as *mut LeanObject],
};
static mut l_Std_Do_triple___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__22_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__23_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__20_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__23_value) as *mut LeanObject;
pub static l_Std_Do_triple___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_triple___closed__3_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_triple___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_triple___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__24_value) as *mut LeanObject;
pub static mut l_Std_Do_triple: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_triple___closed__24_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_triple___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_triple___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__0_value) as *mut LeanObject,13979102795498516556 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__5_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__7_value) as *mut LeanObject,14296711813398647265 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__11_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__13_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__15_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 102, 97, 107, 101, 77, 111, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__17_value) as *mut LeanObject,3838192344338869416 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20_value
) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_triple___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_triple___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__23_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__24_value) as *mut LeanObject,611622866940524098 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__25_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__27_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__28_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__30_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__32_value) as *mut LeanObject,18105168627502861736 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__33_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__35_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__36_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__34_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__37_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__31_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__38_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__29_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__39_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__26_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__40_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__43_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value
) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__46_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47_value
) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51_value
) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52_value
) as *mut LeanObject;
pub static l_Std_Do_unexpandTriple___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Std_Do_unexpandTriple___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__0_value) as *mut LeanObject;
static l_Std_Do_unexpandTriple___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__2_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Do_unexpandTriple___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__3_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Do_unexpandTriple___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__4_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Std_Do_unexpandTriple___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__0_value) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_Std_Do_unexpandTriple___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_unexpandTriple___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21()
-> *mut LeanObject {
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_501_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__20;
    v___x_502_ = l_String_toRawSubstring_x27(v___x_501_);
    return v___x_502_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22()
-> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = lean_unsigned_to_nat(0);
    v___x_504_ = lean_box(0);
    v___x_505_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__18;
    v___x_506_ = l_Lean_addMacroScope(v___x_505_, v___x_504_, v___x_503_);
    return v___x_506_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48()
-> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Array_mkArray0(lean_box(0));
    return v___x_563_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(
    mut v_x_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: u8 = 0;
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: u8 = 0;
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_645_: u8 = 0;
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut v_isSharedCheck_695_: u8 = 0;
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: u8 = 0;
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_716_: u8 = 0;
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_571_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__1;
                lean_inc(v_x_568_);
                v___x_572_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_571_);
                if v___x_572_ == 0 {
                    v___x_573_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__6;
                    lean_inc(v_x_568_);
                    v___x_574_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_573_);
                    if v___x_574_ == 0 {
                        v___x_575_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__8;
                        lean_inc(v_x_568_);
                        v___x_576_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_575_);
                        if v___x_576_ == 0 {
                            v___x_577_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__9;
                            v___x_578_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__10;
                            lean_inc(v_x_568_);
                            v___x_579_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_578_);
                            if v___x_579_ == 0 {
                                v___x_580_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__12;
                                lean_inc(v_x_568_);
                                v___x_581_ = l_Lean_Syntax_isOfKind(v_x_568_, v___x_580_);
                                if v___x_581_ == 0 {
                                    v___x_582_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_582_, 0, v_x_568_);
                                    lean_ctor_set(v___x_582_, 1, v___y_570_);
                                    return v___x_582_;
                                } else {
                                    v___x_583_ = lean_unsigned_to_nat(0);
                                    v___x_584_ = l_Lean_Syntax_getArg(v_x_568_, v___x_583_);
                                    v___x_585_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14;
                                    lean_inc(v___x_584_);
                                    v___x_586_ = l_Lean_Syntax_isOfKind(v___x_584_, v___x_585_);
                                    if v___x_586_ == 0 {
                                        lean_dec(v___x_584_);
                                        v___x_587_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_587_, 0, v_x_568_);
                                        lean_ctor_set(v___x_587_, 1, v___y_570_);
                                        return v___x_587_;
                                    } else {
                                        v___x_588_ = lean_unsigned_to_nat(1);
                                        v___x_589_ = l_Lean_Syntax_getArg(v___x_584_, v___x_588_);
                                        lean_dec(v___x_584_);
                                        v___x_590_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16;
                                        lean_inc(v___x_589_);
                                        v___x_591_ = l_Lean_Syntax_isOfKind(v___x_589_, v___x_590_);
                                        if v___x_591_ == 0 {
                                            lean_dec(v___x_589_);
                                            v___x_592_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_592_, 0, v_x_568_);
                                            lean_ctor_set(v___x_592_, 1, v___y_570_);
                                            return v___x_592_;
                                        } else {
                                            v___x_593_ =
                                                l_Lean_Syntax_getArg(v___x_589_, v___x_583_);
                                            lean_dec(v___x_589_);
                                            v___x_594_ = lean_box(0);
                                            v___x_595_ =
                                                l_Lean_Syntax_matchesIdent(v___x_593_, v___x_594_);
                                            lean_dec(v___x_593_);
                                            if v___x_595_ == 0 {
                                                v___x_596_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v___x_596_, 0, v_x_568_);
                                                lean_ctor_set(v___x_596_, 1, v___y_570_);
                                                return v___x_596_;
                                            } else {
                                                v___x_597_ = lean_unsigned_to_nat(3);
                                                v___x_598_ =
                                                    l_Lean_Syntax_getArg(v_x_568_, v___x_597_);
                                                lean_inc(v___x_598_);
                                                v___x_599_ = l_Lean_Syntax_matchesNull(
                                                    v___x_598_, v___x_588_,
                                                );
                                                if v___x_599_ == 0 {
                                                    lean_dec(v___x_598_);
                                                    v___x_600_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                    lean_ctor_set(v___x_600_, 0, v_x_568_);
                                                    lean_ctor_set(v___x_600_, 1, v___y_570_);
                                                    return v___x_600_;
                                                } else {
                                                    v_P_601_ =
                                                        l_Lean_Syntax_getArg(v_x_568_, v___x_588_);
                                                    lean_dec(v_x_568_);
                                                    v___x_602_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_P_601_, v___y_569_, v___y_570_);
                                                    if lean_obj_tag(v___x_602_) == 0 {
                                                        v_a_603_ = lean_ctor_get(v___x_602_, 0);
                                                        v_a_604_ = lean_ctor_get(v___x_602_, 1);
                                                        v_isSharedCheck_628_ =
                                                            (!lean_is_exclusive(v___x_602_)) as u8;
                                                        if v_isSharedCheck_628_ == 0 {
                                                            v___x_606_ = v___x_602_;
                                                            v_isShared_607_ = v_isSharedCheck_628_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_604_);
                                                            lean_inc(v_a_603_);
                                                            lean_dec(v___x_602_);
                                                            v___x_606_ = lean_box(0);
                                                            v_isShared_607_ = v_isSharedCheck_628_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v___x_598_);
                                                        return v___x_602_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_629_ = lean_unsigned_to_nat(1);
                                v___x_630_ = l_Lean_Syntax_getArg(v_x_568_, v___x_629_);
                                v___x_631_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__47;
                                lean_inc(v___x_630_);
                                v___x_632_ = l_Lean_Syntax_isOfKind(v___x_630_, v___x_631_);
                                if v___x_632_ == 0 {
                                    lean_dec(v___x_630_);
                                    v___x_633_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_633_, 0, v_x_568_);
                                    lean_ctor_set(v___x_633_, 1, v___y_570_);
                                    return v___x_633_;
                                } else {
                                    v___x_634_ = lean_unsigned_to_nat(0);
                                    v___x_635_ = l_Lean_Syntax_getArg(v___x_630_, v___x_629_);
                                    v___x_636_ = l_Lean_Syntax_matchesNull(v___x_635_, v___x_634_);
                                    if v___x_636_ == 0 {
                                        lean_dec(v___x_630_);
                                        v___x_637_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_637_, 0, v_x_568_);
                                        lean_ctor_set(v___x_637_, 1, v___y_570_);
                                        return v___x_637_;
                                    } else {
                                        lean_dec(v_x_568_);
                                        v___x_638_ = lean_unsigned_to_nat(3);
                                        v_b_639_ = l_Lean_Syntax_getArg(v___x_630_, v___x_638_);
                                        v___x_640_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_b_639_, v___y_569_, v___y_570_);
                                        if lean_obj_tag(v___x_640_) == 0 {
                                            v_a_641_ = lean_ctor_get(v___x_640_, 0);
                                            v_a_642_ = lean_ctor_get(v___x_640_, 1);
                                            v_isSharedCheck_662_ =
                                                (!lean_is_exclusive(v___x_640_)) as u8;
                                            if v_isSharedCheck_662_ == 0 {
                                                v___x_644_ = v___x_640_;
                                                v_isShared_645_ = v_isSharedCheck_662_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_642_);
                                                lean_inc(v_a_641_);
                                                lean_dec(v___x_640_);
                                                v___x_644_ = lean_box(0);
                                                v_isShared_645_ = v_isSharedCheck_662_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_630_);
                                            return v___x_640_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_663_ = lean_unsigned_to_nat(3);
                            v_t_664_ = l_Lean_Syntax_getArg(v_x_568_, v___x_663_);
                            v___x_665_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_t_664_, v___y_569_, v___y_570_);
                            if lean_obj_tag(v___x_665_) == 0 {
                                v_a_666_ = lean_ctor_get(v___x_665_, 0);
                                v_a_667_ = lean_ctor_get(v___x_665_, 1);
                                v_isSharedCheck_695_ = (!lean_is_exclusive(v___x_665_)) as u8;
                                if v_isSharedCheck_695_ == 0 {
                                    v___x_669_ = v___x_665_;
                                    v_isShared_670_ = v_isSharedCheck_695_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_667_);
                                    lean_inc(v_a_666_);
                                    lean_dec(v___x_665_);
                                    v___x_669_ = lean_box(0);
                                    v_isShared_670_ = v_isSharedCheck_695_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_x_568_);
                                return v___x_665_;
                            }
                        }
                    } else {
                        v___x_696_ = lean_unsigned_to_nat(0);
                        v___x_697_ = l_Lean_Syntax_getArg(v_x_568_, v___x_696_);
                        v___x_698_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__14;
                        lean_inc(v___x_697_);
                        v___x_699_ = l_Lean_Syntax_isOfKind(v___x_697_, v___x_698_);
                        if v___x_699_ == 0 {
                            lean_dec(v___x_697_);
                            v___x_700_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_700_, 0, v_x_568_);
                            lean_ctor_set(v___x_700_, 1, v___y_570_);
                            return v___x_700_;
                        } else {
                            v___x_701_ = lean_unsigned_to_nat(1);
                            v___x_702_ = l_Lean_Syntax_getArg(v___x_697_, v___x_701_);
                            lean_dec(v___x_697_);
                            v___x_703_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__16;
                            lean_inc(v___x_702_);
                            v___x_704_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_703_);
                            if v___x_704_ == 0 {
                                lean_dec(v___x_702_);
                                v___x_705_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_705_, 0, v_x_568_);
                                lean_ctor_set(v___x_705_, 1, v___y_570_);
                                return v___x_705_;
                            } else {
                                v___x_706_ = l_Lean_Syntax_getArg(v___x_702_, v___x_696_);
                                lean_dec(v___x_702_);
                                v___x_707_ = lean_box(0);
                                v___x_708_ = l_Lean_Syntax_matchesIdent(v___x_706_, v___x_707_);
                                lean_dec(v___x_706_);
                                if v___x_708_ == 0 {
                                    v___x_709_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_709_, 0, v_x_568_);
                                    lean_ctor_set(v___x_709_, 1, v___y_570_);
                                    return v___x_709_;
                                } else {
                                    v_P_710_ = l_Lean_Syntax_getArg(v_x_568_, v___x_701_);
                                    lean_dec(v_x_568_);
                                    v___x_711_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(v_P_710_, v___y_569_, v___y_570_);
                                    if lean_obj_tag(v___x_711_) == 0 {
                                        v_a_712_ = lean_ctor_get(v___x_711_, 0);
                                        v_a_713_ = lean_ctor_get(v___x_711_, 1);
                                        v_isSharedCheck_732_ =
                                            (!lean_is_exclusive(v___x_711_)) as u8;
                                        if v_isSharedCheck_732_ == 0 {
                                            v___x_715_ = v___x_711_;
                                            v_isShared_716_ = v_isSharedCheck_732_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_713_);
                                            lean_inc(v_a_712_);
                                            lean_dec(v___x_711_);
                                            v___x_715_ = lean_box(0);
                                            v_isShared_716_ = v_isSharedCheck_732_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        return v___x_711_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_733_ = lean_unsigned_to_nat(1);
                    v___x_734_ = l_Lean_Syntax_getArg(v_x_568_, v___x_733_);
                    lean_dec(v_x_568_);
                    v___x_735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_735_, 0, v___x_734_);
                    lean_ctor_set(v___x_735_, 1, v___y_570_);
                    return v___x_735_;
                }
            }
            1 => {
                v___x_608_ = l_Lean_Syntax_getArg(v___x_598_, v___x_583_);
                lean_dec(v___x_598_);
                v___x_609_ = l_Lean_SourceInfo_fromRef(v___y_569_, v___x_579_);
                v___x_610_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19;
                lean_inc_n(v___x_609_, 7);
                v___x_611_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_611_, 0, v___x_609_);
                lean_ctor_set(v___x_611_, 1, v___x_610_);
                v___x_612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21);
                v___x_613_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once), _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22);
                v___x_614_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41;
                v___x_615_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_615_, 0, v___x_609_);
                lean_ctor_set(v___x_615_, 1, v___x_612_);
                lean_ctor_set(v___x_615_, 2, v___x_613_);
                lean_ctor_set(v___x_615_, 3, v___x_614_);
                v___x_616_ = l_Lean_Syntax_node1(v___x_609_, v___x_590_, v___x_615_);
                v___x_617_ = l_Lean_Syntax_node2(v___x_609_, v___x_585_, v___x_611_, v___x_616_);
                v___x_618_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__42;
                v___x_619_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_619_, 0, v___x_609_);
                lean_ctor_set(v___x_619_, 1, v___x_618_);
                v___x_620_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44;
                v___x_621_ = l_Lean_Syntax_node1(v___x_609_, v___x_620_, v___x_608_);
                v___x_622_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45;
                v___x_623_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_623_, 0, v___x_609_);
                lean_ctor_set(v___x_623_, 1, v___x_622_);
                v___x_624_ = l_Lean_Syntax_node5(
                    v___x_609_, v___x_580_, v___x_617_, v_a_603_, v___x_619_, v___x_621_,
                    v___x_623_,
                );
                if v_isShared_607_ == 0 {
                    lean_ctor_set(v___x_606_, 0, v___x_624_);
                    v___x_626_ = v___x_606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
                    lean_ctor_set(v_reuseFailAlloc_627_, 1, v_a_604_);
                    v___x_626_ = v_reuseFailAlloc_627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_626_;
            }
            3 => {
                v___x_646_ = l_Lean_Syntax_getArg(v___x_630_, v___x_634_);
                lean_dec(v___x_630_);
                v_xs_647_ = l_Lean_Syntax_getArgs(v___x_646_);
                lean_dec(v___x_646_);
                v___x_648_ = l_Lean_SourceInfo_fromRef(v___y_569_, v___x_576_);
                lean_inc_n(v___x_648_, 5);
                v___x_649_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_649_, 0, v___x_648_);
                lean_ctor_set(v___x_649_, 1, v___x_577_);
                v___x_650_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__44;
                v___x_651_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48_once), _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__48);
                v___x_652_ = l_Array_append___redArg(v___x_651_, v_xs_647_);
                lean_dec_ref(v_xs_647_);
                v___x_653_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_653_, 0, v___x_648_);
                lean_ctor_set(v___x_653_, 1, v___x_650_);
                lean_ctor_set(v___x_653_, 2, v___x_652_);
                v___x_654_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_654_, 0, v___x_648_);
                lean_ctor_set(v___x_654_, 1, v___x_650_);
                lean_ctor_set(v___x_654_, 2, v___x_651_);
                v___x_655_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__49;
                v___x_656_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_656_, 0, v___x_648_);
                lean_ctor_set(v___x_656_, 1, v___x_655_);
                v___x_657_ = l_Lean_Syntax_node4(
                    v___x_648_, v___x_631_, v___x_653_, v___x_654_, v___x_656_, v_a_641_,
                );
                v___x_658_ = l_Lean_Syntax_node2(v___x_648_, v___x_578_, v___x_649_, v___x_657_);
                if v_isShared_645_ == 0 {
                    lean_ctor_set(v___x_644_, 0, v___x_658_);
                    v___x_660_ = v___x_644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
                    lean_ctor_set(v_reuseFailAlloc_661_, 1, v_a_642_);
                    v___x_660_ = v_reuseFailAlloc_661_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_660_;
            }
            5 => {
                v___x_671_ = lean_unsigned_to_nat(5);
                v_e_672_ = l_Lean_Syntax_getArg(v_x_568_, v___x_671_);
                v___x_673_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(
                    v_e_672_, v___y_569_, v_a_667_,
                );
                if lean_obj_tag(v___x_673_) == 0 {
                    v_a_674_ = lean_ctor_get(v___x_673_, 0);
                    v_a_675_ = lean_ctor_get(v___x_673_, 1);
                    v_isSharedCheck_694_ = (!lean_is_exclusive(v___x_673_)) as u8;
                    if v_isSharedCheck_694_ == 0 {
                        v___x_677_ = v___x_673_;
                        v_isShared_678_ = v_isSharedCheck_694_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_675_);
                        lean_inc(v_a_674_);
                        lean_dec(v___x_673_);
                        v___x_677_ = lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_694_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_669_);
                    lean_dec(v_a_666_);
                    lean_dec(v_x_568_);
                    return v___x_673_;
                }
            }
            6 => {
                v___x_679_ = lean_unsigned_to_nat(1);
                v___x_680_ = l_Lean_Syntax_getArg(v_x_568_, v___x_679_);
                lean_dec(v_x_568_);
                v___x_681_ = l_Lean_SourceInfo_fromRef(v___y_569_, v___x_574_);
                v___x_682_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__50;
                lean_inc(v___x_681_);
                if v_isShared_670_ == 0 {
                    lean_ctor_set_tag(v___x_669_, 2);
                    lean_ctor_set(v___x_669_, 1, v___x_682_);
                    lean_ctor_set(v___x_669_, 0, v___x_681_);
                    v___x_684_ = v___x_669_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_681_);
                    lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_682_);
                    v___x_684_ = v_reuseFailAlloc_693_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_685_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__51;
                lean_inc_n(v___x_681_, 2);
                v___x_686_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_686_, 0, v___x_681_);
                lean_ctor_set(v___x_686_, 1, v___x_685_);
                v___x_687_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__52;
                v___x_688_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_688_, 0, v___x_681_);
                lean_ctor_set(v___x_688_, 1, v___x_687_);
                v___x_689_ = l_Lean_Syntax_node6(
                    v___x_681_, v___x_575_, v___x_684_, v___x_680_, v___x_686_, v_a_666_,
                    v___x_688_, v_a_674_,
                );
                if v_isShared_678_ == 0 {
                    lean_ctor_set(v___x_677_, 0, v___x_689_);
                    v___x_691_ = v___x_677_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
                    lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_675_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_691_;
            }
            9 => {
                v___x_717_ = l_Lean_SourceInfo_fromRef(v___y_569_, v___x_572_);
                v___x_718_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__19;
                lean_inc_n(v___x_717_, 5);
                v___x_719_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_719_, 0, v___x_717_);
                lean_ctor_set(v___x_719_, 1, v___x_718_);
                v___x_720_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__21);
                v___x_721_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22_once), _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__22);
                v___x_722_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__41;
                v___x_723_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_723_, 0, v___x_717_);
                lean_ctor_set(v___x_723_, 1, v___x_720_);
                lean_ctor_set(v___x_723_, 2, v___x_721_);
                lean_ctor_set(v___x_723_, 3, v___x_722_);
                v___x_724_ = l_Lean_Syntax_node1(v___x_717_, v___x_703_, v___x_723_);
                v___x_725_ = l_Lean_Syntax_node2(v___x_717_, v___x_698_, v___x_719_, v___x_724_);
                v___x_726_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___closed__45;
                v___x_727_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_727_, 0, v___x_717_);
                lean_ctor_set(v___x_727_, 1, v___x_726_);
                v___x_728_ =
                    l_Lean_Syntax_node3(v___x_717_, v___x_573_, v___x_725_, v_a_712_, v___x_727_);
                if v_isShared_716_ == 0 {
                    lean_ctor_set(v___x_715_, 0, v___x_728_);
                    v___x_730_ = v___x_715_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
                    lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_713_);
                    v___x_730_ = v_reuseFailAlloc_731_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0___boxed(
    mut v_x_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_739_: *mut LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(
        v_x_736_, v___y_737_, v___y_738_,
    );
    lean_dec(v___y_737_);
    return v_res_739_;
}
pub unsafe fn l_Std_Do_unexpandTriple(
    mut v_x_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: u8 = 0;
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_765_: u8 = 0;
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: u8 = 0;
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_781_: u8 = 0;
    let mut v_a_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_749_ = l_Std_Do_unexpandTriple___closed__1;
                lean_inc(v_x_746_);
                v___x_750_ = l_Lean_Syntax_isOfKind(v_x_746_, v___x_749_);
                if v___x_750_ == 0 {
                    lean_dec(v_x_746_);
                    v___x_751_ = lean_box(0);
                    v___x_752_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_752_, 0, v___x_751_);
                    lean_ctor_set(v___x_752_, 1, v_a_748_);
                    return v___x_752_;
                } else {
                    v___x_753_ = lean_unsigned_to_nat(1);
                    v___x_754_ = l_Lean_Syntax_getArg(v_x_746_, v___x_753_);
                    lean_dec(v_x_746_);
                    v___x_755_ = lean_unsigned_to_nat(3);
                    lean_inc(v___x_754_);
                    v___x_756_ = l_Lean_Syntax_matchesNull(v___x_754_, v___x_755_);
                    if v___x_756_ == 0 {
                        lean_dec(v___x_754_);
                        v___x_757_ = lean_box(0);
                        v___x_758_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_758_, 0, v___x_757_);
                        lean_ctor_set(v___x_758_, 1, v_a_748_);
                        return v___x_758_;
                    } else {
                        v_P_759_ = l_Lean_Syntax_getArg(v___x_754_, v___x_753_);
                        v___x_760_ =
                            l_Std_Do_SPred_Notation_unpack___at___00Std_Do_unexpandTriple_spec__0(
                                v_P_759_, v_a_747_, v_a_748_,
                            );
                        if lean_obj_tag(v___x_760_) == 0 {
                            v_a_761_ = lean_ctor_get(v___x_760_, 0);
                            v_a_762_ = lean_ctor_get(v___x_760_, 1);
                            v_isSharedCheck_781_ = (!lean_is_exclusive(v___x_760_)) as u8;
                            if v_isSharedCheck_781_ == 0 {
                                v___x_764_ = v___x_760_;
                                v_isShared_765_ = v_isSharedCheck_781_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_762_);
                                lean_inc(v_a_761_);
                                lean_dec(v___x_760_);
                                v___x_764_ = lean_box(0);
                                v_isShared_765_ = v_isSharedCheck_781_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_754_);
                            v_a_782_ = lean_ctor_get(v___x_760_, 0);
                            v_a_783_ = lean_ctor_get(v___x_760_, 1);
                            v_isSharedCheck_790_ = (!lean_is_exclusive(v___x_760_)) as u8;
                            if v_isSharedCheck_790_ == 0 {
                                v___x_785_ = v___x_760_;
                                v_isShared_786_ = v_isSharedCheck_790_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_783_);
                                lean_inc(v_a_782_);
                                lean_dec(v___x_760_);
                                v___x_785_ = lean_box(0);
                                v_isShared_786_ = v_isSharedCheck_790_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_766_ = lean_unsigned_to_nat(0);
                v___x_767_ = l_Lean_Syntax_getArg(v___x_754_, v___x_766_);
                v___x_768_ = lean_unsigned_to_nat(2);
                v___x_769_ = l_Lean_Syntax_getArg(v___x_754_, v___x_768_);
                lean_dec(v___x_754_);
                v___x_770_ = 0;
                v___x_771_ = l_Lean_SourceInfo_fromRef(v_a_747_, v___x_770_);
                v___x_772_ = l_Std_Do_triple___closed__3;
                v___x_773_ = l_Std_Do_triple___closed__6;
                lean_inc_n(v___x_771_, 2);
                v___x_774_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_774_, 0, v___x_771_);
                lean_ctor_set(v___x_774_, 1, v___x_773_);
                v___x_775_ = l_Std_Do_triple___closed__21;
                v___x_776_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_776_, 0, v___x_771_);
                lean_ctor_set(v___x_776_, 1, v___x_775_);
                lean_inc_ref(v___x_776_);
                lean_inc_ref(v___x_774_);
                v___x_777_ = l_Lean_Syntax_node7(
                    v___x_771_, v___x_772_, v___x_774_, v_a_761_, v___x_776_, v___x_767_,
                    v___x_774_, v___x_769_, v___x_776_,
                );
                if v_isShared_765_ == 0 {
                    lean_ctor_set(v___x_764_, 0, v___x_777_);
                    v___x_779_ = v___x_764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
                    lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_762_);
                    v___x_779_ = v_reuseFailAlloc_780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_779_;
            }
            3 => {
                if v_isShared_786_ == 0 {
                    v___x_788_ = v___x_785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_782_);
                    lean_ctor_set(v_reuseFailAlloc_789_, 1, v_a_783_);
                    v___x_788_ = v_reuseFailAlloc_789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_unexpandTriple___boxed(
    mut v_x_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Std_Do_unexpandTriple(v_x_791_, v_a_792_, v_a_793_);
    lean_dec(v_a_792_);
    return v_res_794_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_Triple_Basic(builtin);
}
