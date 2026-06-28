// Lean compiler output
// Module: Std.Time.Notation.Spec
// Imports: Std.Time.Format.Basic Std.Time.Format.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_push___redArg, l_Lean_Syntax_mkNumLit, l_Lean_Syntax_mkStrLit,
    l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Time::Format::Basic::{
    initialize_Std_Time_Format_Basic, l_Std_Time_GenericFormat_spec___redArg,
    meta_initialize_Std_Time_Format_Basic, runtime_initialize_Std_Time_Format_Basic,
};
use crate::r#gen::Std::Time::Format::DateFormat::l_Std_Time_DateFormat_enUS;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 101, 120, 116, 46, 115, 104, 111, 114, 116, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0_value
)
    as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
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
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 105, 109, 101, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 120, 116, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 104, 111, 114, 116, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value
)
    as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value
        ) as *mut LeanObject,
        13602568763099240109 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value
        ) as *mut LeanObject,
        10330652630996952858 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__8_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__9_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 101, 120, 116, 46, 102, 117, 108, 108, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [102, 117, 108, 108, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value
        ) as *mut LeanObject,
        13602568763099240109 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value
        ) as *mut LeanObject,
        2559842840676049401 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__16_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__15_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__17_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19_value:
    LeanStringObject<21> = LeanStringObject {
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
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 101, 120, 116, 46, 110, 97, 114, 114, 111,
        119, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [110, 97, 114, 114, 111, 119, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__4_value
        ) as *mut LeanObject,
        13602568763099240109 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__21_value
        ) as *mut LeanObject,
        17491816695284868574 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__24_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__23_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__25_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value:
    LeanStringObject<4> = LeanStringObject {
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
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__3_value
        ) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 78, 117, 109, 98, 101, 114, 46, 109, 107, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [78, 117, 109, 98, 101, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__7_value
        ) as *mut LeanObject,
        12199480270274830229 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__8_value
        ) as *mut LeanObject,
        14844594727034214161 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__11_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__10_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__12_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__14_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 70, 114, 97, 99, 116, 105, 111, 110, 46, 110, 97,
        110, 111, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [70, 114, 97, 99, 116, 105, 111, 110, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 97, 110, 111, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value
        ) as *mut LeanObject,
        145338858648146862 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__3_value
        ) as *mut LeanObject,
        2578162016421642887 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__7_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 70, 114, 97, 99, 116, 105, 111, 110, 46, 116, 114,
        117, 110, 99, 97, 116, 101, 100, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 114, 117, 110, 99, 97, 116, 101, 100, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__2_value
        ) as *mut LeanObject,
        145338858648146862 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__11_value
        ) as *mut LeanObject,
        18305134478950855925 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__14_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__15_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 97, 110, 121, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0_value
)
    as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [89, 101, 97, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 110, 121, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value
)
    as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value
        ) as *mut LeanObject,
        4284294970126908753 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__3_value
        ) as *mut LeanObject,
        9720394294361413553 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__7_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8_value
)
    as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 116, 119, 111, 68, 105, 103,
        105, 116, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9_value
)
    as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 119, 111, 68, 105, 103, 105, 116, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value
        ) as *mut LeanObject,
        4284294970126908753 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__11_value
        ) as *mut LeanObject,
        11323318094043880202 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__14_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__15_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17_value:
    LeanStringObject<24> = LeanStringObject {
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
        83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 102, 111, 117, 114, 68, 105,
        103, 105, 116, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [102, 111, 117, 114, 68, 105, 103, 105, 116, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value
        ) as *mut LeanObject,
        4284294970126908753 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__19_value
        ) as *mut LeanObject,
        16436818575018433787 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__22_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__21_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__23_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 101, 120, 116, 101, 110,
        100, 101, 100, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 120, 116, 101, 110, 100, 101, 100, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__2_value
        ) as *mut LeanObject,
        4284294970126908753 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__27_value
        ) as *mut LeanObject,
        15121831023761503405 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__30_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__29_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__31_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0_value:
    LeanStringObject<24> = LeanStringObject {
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
        83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 78, 97, 109, 101, 46, 115, 104,
        111, 114, 116, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [90, 111, 110, 101, 78, 97, 109, 101, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value
        ) as *mut LeanObject,
        1045651794198912495 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value
        ) as *mut LeanObject,
        13534180418020888624 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 78, 97, 109, 101, 46, 102, 117,
        108, 108, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__2_value
        ) as *mut LeanObject,
        1045651794198912495 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value
        ) as *mut LeanObject,
        17353506098478796003 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__11_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__13_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 88, 46, 104, 111,
        117, 114, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [79, 102, 102, 115, 101, 116, 88, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 117, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
        ) as *mut LeanObject,
        11877079720479297864 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__3_value
        ) as *mut LeanObject,
        10597293579225890910 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__7_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 88, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [104, 111, 117, 114, 77, 105, 110, 117, 116, 101, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
        ) as *mut LeanObject,
        11877079720479297864 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value
        ) as *mut LeanObject,
        3582989487426807008 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__14_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__15_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17_value:
    LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 88, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 67, 111, 108, 111, 110, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value:
    LeanStringObject<16> = LeanStringObject {
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
        104, 111, 117, 114, 77, 105, 110, 117, 116, 101, 67, 111, 108, 111, 110, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
        ) as *mut LeanObject,
        11877079720479297864 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__19_value
        ) as *mut LeanObject,
        6816284102736416297 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__22_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__21_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__23_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 88, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 83, 101, 99, 111, 110, 100, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        104, 111, 117, 114, 77, 105, 110, 117, 116, 101, 83, 101, 99, 111, 110, 100, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
        ) as *mut LeanObject,
        11877079720479297864 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__27_value
        ) as *mut LeanObject,
        16970762948813770465 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__30_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__29_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__31_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 88, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 83, 101, 99, 111, 110, 100, 67, 111, 108, 111, 110,
        0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        104, 111, 117, 114, 77, 105, 110, 117, 116, 101, 83, 101, 99, 111, 110, 100, 67, 111, 108,
        111, 110, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__2_value
        ) as *mut LeanObject,
        11877079720479297864 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value
        ) as *mut LeanObject,
        7123390470134111884 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__38_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__39_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 79, 46, 115, 104,
        111, 114, 116, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [79, 102, 102, 115, 101, 116, 79, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value
        ) as *mut LeanObject,
        14977403106375138371 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__5_value
        ) as *mut LeanObject,
        13983505750055626252 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 79, 46, 102, 117,
        108, 108, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__2_value
        ) as *mut LeanObject,
        14977403106375138371 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value
        ) as *mut LeanObject,
        12350477319592661079 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__11_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__13_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 90, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [79, 102, 102, 115, 101, 116, 90, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value
        ) as *mut LeanObject,
        18366844830832171685 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__11_value
        ) as *mut LeanObject,
        6450585761116266769 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 90, 46, 102, 117,
        108, 108, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value
        ) as *mut LeanObject,
        18366844830832171685 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__13_value
        ) as *mut LeanObject,
        13863749040462430881 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__11_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__13_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 79, 102, 102, 115, 101, 116, 90, 46, 104, 111,
        117, 114, 77, 105, 110, 117, 116, 101, 83, 101, 99, 111, 110, 100, 67, 111, 108, 111, 110,
        0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__2_value
        ) as *mut LeanObject,
        18366844830832171685 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__35_value
        ) as *mut LeanObject,
        6325959272407702021 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__19_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__18_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__20_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 71, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [77, 111, 100, 105, 102, 105, 101, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [71, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__3_value
        ) as *mut LeanObject,
        13802089154913799350 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__7_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 121, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [121, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__11_value
        ) as *mut LeanObject,
        12830860983888797555 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__14_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__15_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 117, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [117, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__19_value
        ) as *mut LeanObject,
        16006057311200432275 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__22_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__21_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__23_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 89, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [89, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__27_value
        ) as *mut LeanObject,
        17409224192674994958 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__30_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__29_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__31_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 68, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [68, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__35_value
        ) as *mut LeanObject,
        9445469881604363374 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__38_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__37_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__39_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 77,
        111, 114, 76, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 111, 114, 76, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__43_value
        ) as *mut LeanObject,
        13158481960353548731 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__46_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__45_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__47_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__49_value
        ) as *mut LeanObject,
        7932075773091973500 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__51_value
        ) as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__54_value
        ) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__58_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__60_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__62_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__63_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__65_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__67_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__68_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__66_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__69_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__64_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__70_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__61_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__71_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__59_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__72_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__74_value
        ) as *mut LeanObject,
        14183307858573822893 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 108, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77_value
        ) as *mut LeanObject,
        9527497624779984470 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81_value
        ) as *mut LeanObject,
        7796021816216704209 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 100, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [100, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__86_value
        ) as *mut LeanObject,
        4273999401025777963 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__89_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__88_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__90_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 81,
        111, 114, 113, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [81, 111, 114, 113, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
        ) as *mut LeanObject,
        4964482591384987200 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value
        ) as *mut LeanObject,
        14066822041800305780 as *mut LeanObject,
    ],
};
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__94_value
        ) as *mut LeanObject,
        3351540362820684783 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__97_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__96_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__98_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 119, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [119, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__102_value) as *mut LeanObject,4454814545612077677 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__105_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__104_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__106_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 87, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [87, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__110_value) as *mut LeanObject,17477701362664460942 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__113_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__112_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__114_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 69, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [69, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__118_value) as *mut LeanObject,4029988538862629597 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__121_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__120_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__122_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 101,
        111, 114, 99, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 111, 114, 99, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__126_value) as *mut LeanObject,11717152305154473374 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__129_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__128_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__130_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 70, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [70, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__134_value) as *mut LeanObject,1851038512531156223 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__137_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__136_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__138_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 97, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [97, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__142_value) as *mut LeanObject,14335601476409509156 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__145_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__144_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__146_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 104, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__150_value) as *mut LeanObject,9762124390937400235 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__153_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__152_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__154_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 75, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [75, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__158_value) as *mut LeanObject,17254644482589846959 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__161_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__160_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__162_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 107, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [107, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__166_value) as *mut LeanObject,16129370075321612218 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__169_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__168_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__170_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 72, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [72, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__174_value) as *mut LeanObject,12182818083943030730 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__177_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__176_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__178_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 109, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [109, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__182_value) as *mut LeanObject,2403195969432583798 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__185_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__184_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__186_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 115, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [115, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__190_value) as *mut LeanObject,8007253561258519120 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__193_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__192_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__194_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 83, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [83, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__198_value) as *mut LeanObject,14967204996450577981 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__201_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__200_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__202_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 65, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [65, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__206_value) as *mut LeanObject,12979290251353402110 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__209_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__208_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__210_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 110, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [110, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__214_value) as *mut LeanObject,16813531106249494054 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__217_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__216_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__218_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 78, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [78, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__222_value) as *mut LeanObject,4364783979007510923 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__225_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__224_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__226_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 86, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [86, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__230_value) as *mut LeanObject,324264703060983345 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__233_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__232_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__234_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 122, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [122, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__238_value) as *mut LeanObject,16407074693617670837 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__241_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__240_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__242_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 79, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [79, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__246_value) as *mut LeanObject,2425142126129813306 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__249_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__248_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__250_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 88, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [88, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__254_value) as *mut LeanObject,8777129803393542426 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__257_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__256_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__258_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 120, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__262_value) as *mut LeanObject,5033635767612474056 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__265_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__264_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__266_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 77, 111, 100, 105, 102, 105, 101, 114, 46, 90, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [90, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value) as *mut LeanObject,4964482591384987200 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__2_value) as *mut LeanObject,14066822041800305780 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__270_value) as *mut LeanObject,4779149430570553900 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271_value
    ) as *mut LeanObject],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__273_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__272_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__274_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0_value
        ) as *mut LeanObject,
        12646373330966034450 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 111, 100, 105, 102, 105, 101, 114, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3_value
        ) as *mut LeanObject,
        14538257872626446049 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5_value
) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
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
            116, 101, 114, 109, 68, 97, 116, 101, 115, 112, 101, 99, 40, 95, 41, 0,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__0_value) as *mut LeanObject;
static l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
            ) as *mut LeanObject,
            4964482591384987200 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_termDatespec_x28___x29___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__0_value)
                as *mut LeanObject,
            14739827230989254774 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__2_value: LeanStringObject<8> =
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
static mut l_Std_Time_termDatespec_x28___x29___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__2_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [100, 97, 116, 101, 115, 112, 101, 99, 40, 0],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__6_value: LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__6_value)
                as *mut LeanObject,
            9232979286016572671 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__7_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__8_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__9_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__10_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__11_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x29___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x29___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__12_value) as *mut LeanObject;
pub static mut l_Std_Time_termDatespec_x28___x29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__12_value) as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            116, 101, 114, 109, 68, 97, 116, 101, 115, 112, 101, 99, 40, 95, 44, 95, 41, 0,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value)
        as *mut LeanObject;
static l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__2_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__3_value
            ) as *mut LeanObject,
            4964482591384987200 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__0_value)
                as *mut LeanObject,
            8312338551356475954 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value: LeanStringObject<5> =
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
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__5_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__6_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x29___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_termDatespec_x28___x2c___x29___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value)
        as *mut LeanObject;
pub static mut l_Std_Time_termDatespec_x28___x2c___x29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_termDatespec_x28___x2c___x29___closed__10_value)
        as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 99, 111, 109, 112, 105, 108, 101, 32, 115, 112, 101, 99,
        58, 32, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__3_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 168, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 91, 95, 93, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__6_value
        ) as *mut LeanObject,
        11666683425613976406 as *mut LeanObject,
    ],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8_value
) as *mut LeanObject;
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 101, 114, 109, 123, 125, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__12_value) as *mut LeanObject,5126085667538439468 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__16_value) as *mut LeanObject,2026475204632980274 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__18_value) as *mut LeanObject,5018042693327868416 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value
) as *mut LeanObject;
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__20_value) as *mut LeanObject,11580369617518985485 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value
) as *mut LeanObject;
pub static l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__22_value) as *mut LeanObject,11985596712582660667 as *mut LeanObject] };
static mut l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23_value
) as *mut LeanObject;
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1()
-> *mut LeanObject {
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    v___x_2814_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__0;
    v___x_2815_ = l_String_toRawSubstring_x27(v___x_2814_);
    return v___x_2815_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12()
-> *mut LeanObject {
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    v___x_2837_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__11;
    v___x_2838_ = l_String_toRawSubstring_x27(v___x_2837_);
    return v___x_2838_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20()
-> *mut LeanObject {
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    v___x_2857_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__19;
    v___x_2858_ = l_String_toRawSubstring_x27(v___x_2857_);
    return v___x_2858_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
    mut v_x_2876_: u8,
    mut v_a_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_2876_ {
        0 => {
            let mut v_quotContext_2879_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2880_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2881_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2882_: u8 = 0;
            let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2879_ = lean_ctor_get(v_a_2877_, 1);
            v_currMacroScope_2880_ = lean_ctor_get(v_a_2877_, 2);
            v_ref_2881_ = lean_ctor_get(v_a_2877_, 5);
            v___x_2882_ = 0;
            v___x_2883_ = l_Lean_SourceInfo_fromRef(v_ref_2881_, v___x_2882_);
            v___x_2884_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__1,
            );
            v___x_2885_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__6;
            lean_inc(v_currMacroScope_2880_);
            lean_inc(v_quotContext_2879_);
            v___x_2886_ =
                l_Lean_addMacroScope(v_quotContext_2879_, v___x_2885_, v_currMacroScope_2880_);
            v___x_2887_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__10;
            v___x_2888_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2888_, 0, v___x_2883_);
            lean_ctor_set(v___x_2888_, 1, v___x_2884_);
            lean_ctor_set(v___x_2888_, 2, v___x_2886_);
            lean_ctor_set(v___x_2888_, 3, v___x_2887_);
            v___x_2889_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2889_, 0, v___x_2888_);
            lean_ctor_set(v___x_2889_, 1, v_a_2878_);
            return v___x_2889_;
        }
        1 => {
            let mut v_quotContext_2890_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2891_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2892_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2893_: u8 = 0;
            let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2890_ = lean_ctor_get(v_a_2877_, 1);
            v_currMacroScope_2891_ = lean_ctor_get(v_a_2877_, 2);
            v_ref_2892_ = lean_ctor_get(v_a_2877_, 5);
            v___x_2893_ = 0;
            v___x_2894_ = l_Lean_SourceInfo_fromRef(v_ref_2892_, v___x_2893_);
            v___x_2895_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__12,
            );
            v___x_2896_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__14;
            lean_inc(v_currMacroScope_2891_);
            lean_inc(v_quotContext_2890_);
            v___x_2897_ =
                l_Lean_addMacroScope(v_quotContext_2890_, v___x_2896_, v_currMacroScope_2891_);
            v___x_2898_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__18;
            v___x_2899_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2899_, 0, v___x_2894_);
            lean_ctor_set(v___x_2899_, 1, v___x_2895_);
            lean_ctor_set(v___x_2899_, 2, v___x_2897_);
            lean_ctor_set(v___x_2899_, 3, v___x_2898_);
            v___x_2900_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2900_, 0, v___x_2899_);
            lean_ctor_set(v___x_2900_, 1, v_a_2878_);
            return v___x_2900_;
        }
        _ => {
            let mut v_quotContext_2901_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2902_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2903_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2904_: u8 = 0;
            let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2901_ = lean_ctor_get(v_a_2877_, 1);
            v_currMacroScope_2902_ = lean_ctor_get(v_a_2877_, 2);
            v_ref_2903_ = lean_ctor_get(v_a_2877_, 5);
            v___x_2904_ = 0;
            v___x_2905_ = l_Lean_SourceInfo_fromRef(v_ref_2903_, v___x_2904_);
            v___x_2906_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__20,
            );
            v___x_2907_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__22;
            lean_inc(v_currMacroScope_2902_);
            lean_inc(v_quotContext_2901_);
            v___x_2908_ =
                l_Lean_addMacroScope(v_quotContext_2901_, v___x_2907_, v_currMacroScope_2902_);
            v___x_2909_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___closed__26;
            v___x_2910_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2910_, 0, v___x_2905_);
            lean_ctor_set(v___x_2910_, 1, v___x_2906_);
            lean_ctor_set(v___x_2910_, 2, v___x_2908_);
            lean_ctor_set(v___x_2910_, 3, v___x_2909_);
            v___x_2911_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2911_, 0, v___x_2910_);
            lean_ctor_set(v___x_2911_, 1, v_a_2878_);
            return v___x_2911_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertText___boxed(
    mut v_x_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4038__boxed_2915_: u8 = 0;
    let mut v_res_2916_: *mut LeanObject = core::ptr::null_mut();
    v_x_4038__boxed_2915_ = (lean_unbox(v_x_2912_) as u8);
    v_res_2916_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
        v_x_4038__boxed_2915_,
        v_a_2913_,
        v_a_2914_,
    );
    lean_dec_ref(v_a_2913_);
    return v_res_2916_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6()
-> *mut LeanObject {
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    v___x_2927_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__5;
    v___x_2928_ = l_String_toRawSubstring_x27(v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
    mut v_x_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_2953_ = lean_ctor_get(v_a_2951_, 1);
    v_currMacroScope_2954_ = lean_ctor_get(v_a_2951_, 2);
    v_ref_2955_ = lean_ctor_get(v_a_2951_, 5);
    v___x_2956_ = 0;
    v___x_2957_ = l_Lean_SourceInfo_fromRef(v_ref_2955_, v___x_2956_);
    v___x_2958_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
    v___x_2959_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6_once
        ),
        _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__6,
    );
    v___x_2960_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__9;
    lean_inc(v_currMacroScope_2954_);
    lean_inc(v_quotContext_2953_);
    v___x_2961_ = l_Lean_addMacroScope(v_quotContext_2953_, v___x_2960_, v_currMacroScope_2954_);
    v___x_2962_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__13;
    lean_inc_n(v___x_2957_, 2);
    v___x_2963_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_2963_, 0, v___x_2957_);
    lean_ctor_set(v___x_2963_, 1, v___x_2959_);
    lean_ctor_set(v___x_2963_, 2, v___x_2961_);
    lean_ctor_set(v___x_2963_, 3, v___x_2962_);
    v___x_2964_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
    v___x_2965_ = l_Nat_reprFast(v_x_2950_);
    v___x_2966_ = lean_box(2);
    v___x_2967_ = l_Lean_Syntax_mkNumLit(v___x_2965_, v___x_2966_);
    v___x_2968_ = l_Lean_Syntax_node1(v___x_2957_, v___x_2964_, v___x_2967_);
    v___x_2969_ = l_Lean_Syntax_node2(v___x_2957_, v___x_2958_, v___x_2963_, v___x_2968_);
    v___x_2970_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2970_, 0, v___x_2969_);
    lean_ctor_set(v___x_2970_, 1, v_a_2952_);
    return v___x_2970_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___boxed(
    mut v_x_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2974_: *mut LeanObject = core::ptr::null_mut();
    v_res_2974_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
        v_x_2971_, v_a_2972_, v_a_2973_,
    );
    lean_dec_ref(v_a_2972_);
    return v_res_2974_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1()
-> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__0;
    v___x_2977_ = l_String_toRawSubstring_x27(v___x_2976_);
    return v___x_2977_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10()
-> *mut LeanObject {
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    v___x_2997_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__9;
    v___x_2998_ = l_String_toRawSubstring_x27(v___x_2997_);
    return v___x_2998_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(
    mut v_x_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3016_) == 0 {
        let mut v_quotContext_3019_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3020_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3022_: u8 = 0;
        let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3019_ = lean_ctor_get(v_a_3017_, 1);
        v_currMacroScope_3020_ = lean_ctor_get(v_a_3017_, 2);
        v_ref_3021_ = lean_ctor_get(v_a_3017_, 5);
        v___x_3022_ = 0;
        v___x_3023_ = l_Lean_SourceInfo_fromRef(v_ref_3021_, v___x_3022_);
        v___x_3024_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__1,
        );
        v___x_3025_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__4;
        lean_inc(v_currMacroScope_3020_);
        lean_inc(v_quotContext_3019_);
        v___x_3026_ =
            l_Lean_addMacroScope(v_quotContext_3019_, v___x_3025_, v_currMacroScope_3020_);
        v___x_3027_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__8;
        v___x_3028_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3028_, 0, v___x_3023_);
        lean_ctor_set(v___x_3028_, 1, v___x_3024_);
        lean_ctor_set(v___x_3028_, 2, v___x_3026_);
        lean_ctor_set(v___x_3028_, 3, v___x_3027_);
        v___x_3029_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3029_, 0, v___x_3028_);
        lean_ctor_set(v___x_3029_, 1, v_a_3018_);
        return v___x_3029_;
    } else {
        let mut v_digits_3030_: *mut LeanObject = core::ptr::null_mut();
        let mut v_quotContext_3031_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3032_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3034_: u8 = 0;
        let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
        v_digits_3030_ = lean_ctor_get(v_x_3016_, 0);
        lean_inc(v_digits_3030_);
        lean_dec_ref_known(v_x_3016_, 1);
        v_quotContext_3031_ = lean_ctor_get(v_a_3017_, 1);
        v_currMacroScope_3032_ = lean_ctor_get(v_a_3017_, 2);
        v_ref_3033_ = lean_ctor_get(v_a_3017_, 5);
        v___x_3034_ = 0;
        v___x_3035_ = l_Lean_SourceInfo_fromRef(v_ref_3033_, v___x_3034_);
        v___x_3036_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
        v___x_3037_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__10,
        );
        v___x_3038_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__12;
        lean_inc(v_currMacroScope_3032_);
        lean_inc(v_quotContext_3031_);
        v___x_3039_ =
            l_Lean_addMacroScope(v_quotContext_3031_, v___x_3038_, v_currMacroScope_3032_);
        v___x_3040_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___closed__16;
        lean_inc_n(v___x_3035_, 2);
        v___x_3041_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3041_, 0, v___x_3035_);
        lean_ctor_set(v___x_3041_, 1, v___x_3037_);
        lean_ctor_set(v___x_3041_, 2, v___x_3039_);
        lean_ctor_set(v___x_3041_, 3, v___x_3040_);
        v___x_3042_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
        v___x_3043_ = l_Nat_reprFast(v_digits_3030_);
        v___x_3044_ = lean_box(2);
        v___x_3045_ = l_Lean_Syntax_mkNumLit(v___x_3043_, v___x_3044_);
        v___x_3046_ = l_Lean_Syntax_node1(v___x_3035_, v___x_3042_, v___x_3045_);
        v___x_3047_ = l_Lean_Syntax_node2(v___x_3035_, v___x_3036_, v___x_3041_, v___x_3046_);
        v___x_3048_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3048_, 0, v___x_3047_);
        lean_ctor_set(v___x_3048_, 1, v_a_3018_);
        return v___x_3048_;
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction___boxed(
    mut v_x_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3052_: *mut LeanObject = core::ptr::null_mut();
    v_res_3052_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(
        v_x_3049_, v_a_3050_, v_a_3051_,
    );
    lean_dec_ref(v_a_3050_);
    return v_res_3052_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1()
-> *mut LeanObject {
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    v___x_3054_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__0;
    v___x_3055_ = l_String_toRawSubstring_x27(v___x_3054_);
    return v___x_3055_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10()
-> *mut LeanObject {
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    v___x_3075_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__9;
    v___x_3076_ = l_String_toRawSubstring_x27(v___x_3075_);
    return v___x_3076_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18()
-> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    v___x_3095_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__17;
    v___x_3096_ = l_String_toRawSubstring_x27(v___x_3095_);
    return v___x_3096_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26()
-> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    v___x_3115_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__25;
    v___x_3116_ = l_String_toRawSubstring_x27(v___x_3115_);
    return v___x_3116_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(
    mut v_x_3134_: *mut LeanObject,
    mut v_a_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3134_) {
        0 => {
            let mut v_quotContext_3137_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3138_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3139_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3140_: u8 = 0;
            let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3137_ = lean_ctor_get(v_a_3135_, 1);
            v_currMacroScope_3138_ = lean_ctor_get(v_a_3135_, 2);
            v_ref_3139_ = lean_ctor_get(v_a_3135_, 5);
            v___x_3140_ = 0;
            v___x_3141_ = l_Lean_SourceInfo_fromRef(v_ref_3139_, v___x_3140_);
            v___x_3142_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__1,
            );
            v___x_3143_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__4;
            lean_inc(v_currMacroScope_3138_);
            lean_inc(v_quotContext_3137_);
            v___x_3144_ =
                l_Lean_addMacroScope(v_quotContext_3137_, v___x_3143_, v_currMacroScope_3138_);
            v___x_3145_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__8;
            v___x_3146_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3146_, 0, v___x_3141_);
            lean_ctor_set(v___x_3146_, 1, v___x_3142_);
            lean_ctor_set(v___x_3146_, 2, v___x_3144_);
            lean_ctor_set(v___x_3146_, 3, v___x_3145_);
            v___x_3147_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3147_, 0, v___x_3146_);
            lean_ctor_set(v___x_3147_, 1, v_a_3136_);
            return v___x_3147_;
        }
        1 => {
            let mut v_quotContext_3148_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3149_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3151_: u8 = 0;
            let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3148_ = lean_ctor_get(v_a_3135_, 1);
            v_currMacroScope_3149_ = lean_ctor_get(v_a_3135_, 2);
            v_ref_3150_ = lean_ctor_get(v_a_3135_, 5);
            v___x_3151_ = 0;
            v___x_3152_ = l_Lean_SourceInfo_fromRef(v_ref_3150_, v___x_3151_);
            v___x_3153_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__10,
            );
            v___x_3154_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__12;
            lean_inc(v_currMacroScope_3149_);
            lean_inc(v_quotContext_3148_);
            v___x_3155_ =
                l_Lean_addMacroScope(v_quotContext_3148_, v___x_3154_, v_currMacroScope_3149_);
            v___x_3156_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__16;
            v___x_3157_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3157_, 0, v___x_3152_);
            lean_ctor_set(v___x_3157_, 1, v___x_3153_);
            lean_ctor_set(v___x_3157_, 2, v___x_3155_);
            lean_ctor_set(v___x_3157_, 3, v___x_3156_);
            v___x_3158_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3158_, 0, v___x_3157_);
            lean_ctor_set(v___x_3158_, 1, v_a_3136_);
            return v___x_3158_;
        }
        2 => {
            let mut v_quotContext_3159_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3160_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3161_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3162_: u8 = 0;
            let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3159_ = lean_ctor_get(v_a_3135_, 1);
            v_currMacroScope_3160_ = lean_ctor_get(v_a_3135_, 2);
            v_ref_3161_ = lean_ctor_get(v_a_3135_, 5);
            v___x_3162_ = 0;
            v___x_3163_ = l_Lean_SourceInfo_fromRef(v_ref_3161_, v___x_3162_);
            v___x_3164_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__18,
            );
            v___x_3165_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__20;
            lean_inc(v_currMacroScope_3160_);
            lean_inc(v_quotContext_3159_);
            v___x_3166_ =
                l_Lean_addMacroScope(v_quotContext_3159_, v___x_3165_, v_currMacroScope_3160_);
            v___x_3167_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__24;
            v___x_3168_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3168_, 0, v___x_3163_);
            lean_ctor_set(v___x_3168_, 1, v___x_3164_);
            lean_ctor_set(v___x_3168_, 2, v___x_3166_);
            lean_ctor_set(v___x_3168_, 3, v___x_3167_);
            v___x_3169_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3169_, 0, v___x_3168_);
            lean_ctor_set(v___x_3169_, 1, v_a_3136_);
            return v___x_3169_;
        }
        _ => {
            let mut v_num_3170_: *mut LeanObject = core::ptr::null_mut();
            let mut v_quotContext_3171_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3174_: u8 = 0;
            let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
            v_num_3170_ = lean_ctor_get(v_x_3134_, 0);
            lean_inc(v_num_3170_);
            lean_dec_ref_known(v_x_3134_, 1);
            v_quotContext_3171_ = lean_ctor_get(v_a_3135_, 1);
            v_currMacroScope_3172_ = lean_ctor_get(v_a_3135_, 2);
            v_ref_3173_ = lean_ctor_get(v_a_3135_, 5);
            v___x_3174_ = 0;
            v___x_3175_ = l_Lean_SourceInfo_fromRef(v_ref_3173_, v___x_3174_);
            v___x_3176_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
            v___x_3177_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__26,
            );
            v___x_3178_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__28;
            lean_inc(v_currMacroScope_3172_);
            lean_inc(v_quotContext_3171_);
            v___x_3179_ =
                l_Lean_addMacroScope(v_quotContext_3171_, v___x_3178_, v_currMacroScope_3172_);
            v___x_3180_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___closed__32;
            lean_inc_n(v___x_3175_, 2);
            v___x_3181_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3181_, 0, v___x_3175_);
            lean_ctor_set(v___x_3181_, 1, v___x_3177_);
            lean_ctor_set(v___x_3181_, 2, v___x_3179_);
            lean_ctor_set(v___x_3181_, 3, v___x_3180_);
            v___x_3182_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
            v___x_3183_ = l_Nat_reprFast(v_num_3170_);
            v___x_3184_ = lean_box(2);
            v___x_3185_ = l_Lean_Syntax_mkNumLit(v___x_3183_, v___x_3184_);
            v___x_3186_ = l_Lean_Syntax_node1(v___x_3175_, v___x_3182_, v___x_3185_);
            v___x_3187_ = l_Lean_Syntax_node2(v___x_3175_, v___x_3176_, v___x_3181_, v___x_3186_);
            v___x_3188_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3188_, 0, v___x_3187_);
            lean_ctor_set(v___x_3188_, 1, v_a_3136_);
            return v___x_3188_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear___boxed(
    mut v_x_3189_: *mut LeanObject,
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3192_: *mut LeanObject = core::ptr::null_mut();
    v_res_3192_ =
        l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(v_x_3189_, v_a_3190_, v_a_3191_);
    lean_dec_ref(v_a_3190_);
    return v_res_3192_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1()
-> *mut LeanObject {
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    v___x_3194_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__0;
    v___x_3195_ = l_String_toRawSubstring_x27(v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9()
-> *mut LeanObject {
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    v___x_3214_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__8;
    v___x_3215_ = l_String_toRawSubstring_x27(v___x_3214_);
    return v___x_3215_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(
    mut v_x_3232_: u8,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_3232_ == 0 {
        let mut v_quotContext_3235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3238_: u8 = 0;
        let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3235_ = lean_ctor_get(v_a_3233_, 1);
        v_currMacroScope_3236_ = lean_ctor_get(v_a_3233_, 2);
        v_ref_3237_ = lean_ctor_get(v_a_3233_, 5);
        v___x_3238_ = 0;
        v___x_3239_ = l_Lean_SourceInfo_fromRef(v_ref_3237_, v___x_3238_);
        v___x_3240_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__1,
        );
        v___x_3241_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__3;
        lean_inc(v_currMacroScope_3236_);
        lean_inc(v_quotContext_3235_);
        v___x_3242_ =
            l_Lean_addMacroScope(v_quotContext_3235_, v___x_3241_, v_currMacroScope_3236_);
        v___x_3243_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__7;
        v___x_3244_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3244_, 0, v___x_3239_);
        lean_ctor_set(v___x_3244_, 1, v___x_3240_);
        lean_ctor_set(v___x_3244_, 2, v___x_3242_);
        lean_ctor_set(v___x_3244_, 3, v___x_3243_);
        v___x_3245_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3245_, 0, v___x_3244_);
        lean_ctor_set(v___x_3245_, 1, v_a_3234_);
        return v___x_3245_;
    } else {
        let mut v_quotContext_3246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3247_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3249_: u8 = 0;
        let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3246_ = lean_ctor_get(v_a_3233_, 1);
        v_currMacroScope_3247_ = lean_ctor_get(v_a_3233_, 2);
        v_ref_3248_ = lean_ctor_get(v_a_3233_, 5);
        v___x_3249_ = 0;
        v___x_3250_ = l_Lean_SourceInfo_fromRef(v_ref_3248_, v___x_3249_);
        v___x_3251_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__9,
        );
        v___x_3252_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__10;
        lean_inc(v_currMacroScope_3247_);
        lean_inc(v_quotContext_3246_);
        v___x_3253_ =
            l_Lean_addMacroScope(v_quotContext_3246_, v___x_3252_, v_currMacroScope_3247_);
        v___x_3254_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___closed__14;
        v___x_3255_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3255_, 0, v___x_3250_);
        lean_ctor_set(v___x_3255_, 1, v___x_3251_);
        lean_ctor_set(v___x_3255_, 2, v___x_3253_);
        lean_ctor_set(v___x_3255_, 3, v___x_3254_);
        v___x_3256_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3256_, 0, v___x_3255_);
        lean_ctor_set(v___x_3256_, 1, v_a_3234_);
        return v___x_3256_;
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName___boxed(
    mut v_x_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2693__boxed_3260_: u8 = 0;
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
    v_x_2693__boxed_3260_ = (lean_unbox(v_x_3257_) as u8);
    v_res_3261_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(
        v_x_2693__boxed_3260_,
        v_a_3258_,
        v_a_3259_,
    );
    lean_dec_ref(v_a_3258_);
    return v_res_3261_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__0;
    v___x_3264_ = l_String_toRawSubstring_x27(v___x_3263_);
    return v___x_3264_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10()
-> *mut LeanObject {
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3284_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__9;
    v___x_3285_ = l_String_toRawSubstring_x27(v___x_3284_);
    return v___x_3285_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18()
-> *mut LeanObject {
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    v___x_3304_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__17;
    v___x_3305_ = l_String_toRawSubstring_x27(v___x_3304_);
    return v___x_3305_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26()
-> *mut LeanObject {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__25;
    v___x_3325_ = l_String_toRawSubstring_x27(v___x_3324_);
    return v___x_3325_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34()
-> *mut LeanObject {
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3344_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__33;
    v___x_3345_ = l_String_toRawSubstring_x27(v___x_3344_);
    return v___x_3345_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(
    mut v_x_3363_: u8,
    mut v_a_3364_: *mut LeanObject,
    mut v_a_3365_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3363_ {
        0 => {
            let mut v_quotContext_3366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3367_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3368_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3369_: u8 = 0;
            let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3366_ = lean_ctor_get(v_a_3364_, 1);
            v_currMacroScope_3367_ = lean_ctor_get(v_a_3364_, 2);
            v_ref_3368_ = lean_ctor_get(v_a_3364_, 5);
            v___x_3369_ = 0;
            v___x_3370_ = l_Lean_SourceInfo_fromRef(v_ref_3368_, v___x_3369_);
            v___x_3371_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__1,
            );
            v___x_3372_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__4;
            lean_inc(v_currMacroScope_3367_);
            lean_inc(v_quotContext_3366_);
            v___x_3373_ =
                l_Lean_addMacroScope(v_quotContext_3366_, v___x_3372_, v_currMacroScope_3367_);
            v___x_3374_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__8;
            v___x_3375_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3375_, 0, v___x_3370_);
            lean_ctor_set(v___x_3375_, 1, v___x_3371_);
            lean_ctor_set(v___x_3375_, 2, v___x_3373_);
            lean_ctor_set(v___x_3375_, 3, v___x_3374_);
            v___x_3376_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3376_, 0, v___x_3375_);
            lean_ctor_set(v___x_3376_, 1, v_a_3365_);
            return v___x_3376_;
        }
        1 => {
            let mut v_quotContext_3377_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3378_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3380_: u8 = 0;
            let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3377_ = lean_ctor_get(v_a_3364_, 1);
            v_currMacroScope_3378_ = lean_ctor_get(v_a_3364_, 2);
            v_ref_3379_ = lean_ctor_get(v_a_3364_, 5);
            v___x_3380_ = 0;
            v___x_3381_ = l_Lean_SourceInfo_fromRef(v_ref_3379_, v___x_3380_);
            v___x_3382_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__10,
            );
            v___x_3383_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__12;
            lean_inc(v_currMacroScope_3378_);
            lean_inc(v_quotContext_3377_);
            v___x_3384_ =
                l_Lean_addMacroScope(v_quotContext_3377_, v___x_3383_, v_currMacroScope_3378_);
            v___x_3385_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__16;
            v___x_3386_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3386_, 0, v___x_3381_);
            lean_ctor_set(v___x_3386_, 1, v___x_3382_);
            lean_ctor_set(v___x_3386_, 2, v___x_3384_);
            lean_ctor_set(v___x_3386_, 3, v___x_3385_);
            v___x_3387_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3387_, 0, v___x_3386_);
            lean_ctor_set(v___x_3387_, 1, v_a_3365_);
            return v___x_3387_;
        }
        2 => {
            let mut v_quotContext_3388_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3389_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3390_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3391_: u8 = 0;
            let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3388_ = lean_ctor_get(v_a_3364_, 1);
            v_currMacroScope_3389_ = lean_ctor_get(v_a_3364_, 2);
            v_ref_3390_ = lean_ctor_get(v_a_3364_, 5);
            v___x_3391_ = 0;
            v___x_3392_ = l_Lean_SourceInfo_fromRef(v_ref_3390_, v___x_3391_);
            v___x_3393_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__18,
            );
            v___x_3394_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__20;
            lean_inc(v_currMacroScope_3389_);
            lean_inc(v_quotContext_3388_);
            v___x_3395_ =
                l_Lean_addMacroScope(v_quotContext_3388_, v___x_3394_, v_currMacroScope_3389_);
            v___x_3396_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__24;
            v___x_3397_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3397_, 0, v___x_3392_);
            lean_ctor_set(v___x_3397_, 1, v___x_3393_);
            lean_ctor_set(v___x_3397_, 2, v___x_3395_);
            lean_ctor_set(v___x_3397_, 3, v___x_3396_);
            v___x_3398_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3398_, 0, v___x_3397_);
            lean_ctor_set(v___x_3398_, 1, v_a_3365_);
            return v___x_3398_;
        }
        3 => {
            let mut v_quotContext_3399_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3400_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3401_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: u8 = 0;
            let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3399_ = lean_ctor_get(v_a_3364_, 1);
            v_currMacroScope_3400_ = lean_ctor_get(v_a_3364_, 2);
            v_ref_3401_ = lean_ctor_get(v_a_3364_, 5);
            v___x_3402_ = 0;
            v___x_3403_ = l_Lean_SourceInfo_fromRef(v_ref_3401_, v___x_3402_);
            v___x_3404_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__26,
            );
            v___x_3405_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__28;
            lean_inc(v_currMacroScope_3400_);
            lean_inc(v_quotContext_3399_);
            v___x_3406_ =
                l_Lean_addMacroScope(v_quotContext_3399_, v___x_3405_, v_currMacroScope_3400_);
            v___x_3407_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__32;
            v___x_3408_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3408_, 0, v___x_3403_);
            lean_ctor_set(v___x_3408_, 1, v___x_3404_);
            lean_ctor_set(v___x_3408_, 2, v___x_3406_);
            lean_ctor_set(v___x_3408_, 3, v___x_3407_);
            v___x_3409_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3409_, 0, v___x_3408_);
            lean_ctor_set(v___x_3409_, 1, v_a_3365_);
            return v___x_3409_;
        }
        _ => {
            let mut v_quotContext_3410_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3411_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3412_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3413_: u8 = 0;
            let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3410_ = lean_ctor_get(v_a_3364_, 1);
            v_currMacroScope_3411_ = lean_ctor_get(v_a_3364_, 2);
            v_ref_3412_ = lean_ctor_get(v_a_3364_, 5);
            v___x_3413_ = 0;
            v___x_3414_ = l_Lean_SourceInfo_fromRef(v_ref_3412_, v___x_3413_);
            v___x_3415_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__34,
            );
            v___x_3416_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__36;
            lean_inc(v_currMacroScope_3411_);
            lean_inc(v_quotContext_3410_);
            v___x_3417_ =
                l_Lean_addMacroScope(v_quotContext_3410_, v___x_3416_, v_currMacroScope_3411_);
            v___x_3418_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___closed__40;
            v___x_3419_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3419_, 0, v___x_3414_);
            lean_ctor_set(v___x_3419_, 1, v___x_3415_);
            lean_ctor_set(v___x_3419_, 2, v___x_3417_);
            lean_ctor_set(v___x_3419_, 3, v___x_3418_);
            v___x_3420_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3420_, 0, v___x_3419_);
            lean_ctor_set(v___x_3420_, 1, v_a_3365_);
            return v___x_3420_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX___boxed(
    mut v_x_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6718__boxed_3424_: u8 = 0;
    let mut v_res_3425_: *mut LeanObject = core::ptr::null_mut();
    v_x_6718__boxed_3424_ = (lean_unbox(v_x_3421_) as u8);
    v_res_3425_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(
        v_x_6718__boxed_3424_,
        v_a_3422_,
        v_a_3423_,
    );
    lean_dec_ref(v_a_3422_);
    return v_res_3425_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1()
-> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__0;
    v___x_3428_ = l_String_toRawSubstring_x27(v___x_3427_);
    return v___x_3428_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9()
-> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___x_3447_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__8;
    v___x_3448_ = l_String_toRawSubstring_x27(v___x_3447_);
    return v___x_3448_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(
    mut v_x_3465_: u8,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_3465_ == 0 {
        let mut v_quotContext_3468_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3469_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3471_: u8 = 0;
        let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3468_ = lean_ctor_get(v_a_3466_, 1);
        v_currMacroScope_3469_ = lean_ctor_get(v_a_3466_, 2);
        v_ref_3470_ = lean_ctor_get(v_a_3466_, 5);
        v___x_3471_ = 0;
        v___x_3472_ = l_Lean_SourceInfo_fromRef(v_ref_3470_, v___x_3471_);
        v___x_3473_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__1,
        );
        v___x_3474_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__3;
        lean_inc(v_currMacroScope_3469_);
        lean_inc(v_quotContext_3468_);
        v___x_3475_ =
            l_Lean_addMacroScope(v_quotContext_3468_, v___x_3474_, v_currMacroScope_3469_);
        v___x_3476_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__7;
        v___x_3477_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3477_, 0, v___x_3472_);
        lean_ctor_set(v___x_3477_, 1, v___x_3473_);
        lean_ctor_set(v___x_3477_, 2, v___x_3475_);
        lean_ctor_set(v___x_3477_, 3, v___x_3476_);
        v___x_3478_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3478_, 0, v___x_3477_);
        lean_ctor_set(v___x_3478_, 1, v_a_3467_);
        return v___x_3478_;
    } else {
        let mut v_quotContext_3479_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3480_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3482_: u8 = 0;
        let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3479_ = lean_ctor_get(v_a_3466_, 1);
        v_currMacroScope_3480_ = lean_ctor_get(v_a_3466_, 2);
        v_ref_3481_ = lean_ctor_get(v_a_3466_, 5);
        v___x_3482_ = 0;
        v___x_3483_ = l_Lean_SourceInfo_fromRef(v_ref_3481_, v___x_3482_);
        v___x_3484_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9
            ),
            core::ptr::addr_of_mut!(
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9_once
            ),
            _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__9,
        );
        v___x_3485_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__10;
        lean_inc(v_currMacroScope_3480_);
        lean_inc(v_quotContext_3479_);
        v___x_3486_ =
            l_Lean_addMacroScope(v_quotContext_3479_, v___x_3485_, v_currMacroScope_3480_);
        v___x_3487_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___closed__14;
        v___x_3488_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3488_, 0, v___x_3483_);
        lean_ctor_set(v___x_3488_, 1, v___x_3484_);
        lean_ctor_set(v___x_3488_, 2, v___x_3486_);
        lean_ctor_set(v___x_3488_, 3, v___x_3487_);
        v___x_3489_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3489_, 0, v___x_3488_);
        lean_ctor_set(v___x_3489_, 1, v_a_3467_);
        return v___x_3489_;
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO___boxed(
    mut v_x_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2693__boxed_3493_: u8 = 0;
    let mut v_res_3494_: *mut LeanObject = core::ptr::null_mut();
    v_x_2693__boxed_3493_ = (lean_unbox(v_x_3490_) as u8);
    v_res_3494_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(
        v_x_2693__boxed_3493_,
        v_a_3491_,
        v_a_3492_,
    );
    lean_dec_ref(v_a_3491_);
    return v_res_3494_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1()
-> *mut LeanObject {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3496_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__0;
    v___x_3497_ = l_String_toRawSubstring_x27(v___x_3496_);
    return v___x_3497_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9()
-> *mut LeanObject {
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v___x_3516_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__8;
    v___x_3517_ = l_String_toRawSubstring_x27(v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16()
-> *mut LeanObject {
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    v___x_3535_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__15;
    v___x_3536_ = l_String_toRawSubstring_x27(v___x_3535_);
    return v___x_3536_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(
    mut v_x_3553_: u8,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_3553_ {
        0 => {
            let mut v_quotContext_3556_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3557_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3559_: u8 = 0;
            let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3556_ = lean_ctor_get(v_a_3554_, 1);
            v_currMacroScope_3557_ = lean_ctor_get(v_a_3554_, 2);
            v_ref_3558_ = lean_ctor_get(v_a_3554_, 5);
            v___x_3559_ = 0;
            v___x_3560_ = l_Lean_SourceInfo_fromRef(v_ref_3558_, v___x_3559_);
            v___x_3561_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__1,
            );
            v___x_3562_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__3;
            lean_inc(v_currMacroScope_3557_);
            lean_inc(v_quotContext_3556_);
            v___x_3563_ =
                l_Lean_addMacroScope(v_quotContext_3556_, v___x_3562_, v_currMacroScope_3557_);
            v___x_3564_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__7;
            v___x_3565_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3565_, 0, v___x_3560_);
            lean_ctor_set(v___x_3565_, 1, v___x_3561_);
            lean_ctor_set(v___x_3565_, 2, v___x_3563_);
            lean_ctor_set(v___x_3565_, 3, v___x_3564_);
            v___x_3566_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3566_, 0, v___x_3565_);
            lean_ctor_set(v___x_3566_, 1, v_a_3555_);
            return v___x_3566_;
        }
        1 => {
            let mut v_quotContext_3567_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3568_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3570_: u8 = 0;
            let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3567_ = lean_ctor_get(v_a_3554_, 1);
            v_currMacroScope_3568_ = lean_ctor_get(v_a_3554_, 2);
            v_ref_3569_ = lean_ctor_get(v_a_3554_, 5);
            v___x_3570_ = 0;
            v___x_3571_ = l_Lean_SourceInfo_fromRef(v_ref_3569_, v___x_3570_);
            v___x_3572_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__9,
            );
            v___x_3573_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__10;
            lean_inc(v_currMacroScope_3568_);
            lean_inc(v_quotContext_3567_);
            v___x_3574_ =
                l_Lean_addMacroScope(v_quotContext_3567_, v___x_3573_, v_currMacroScope_3568_);
            v___x_3575_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__14;
            v___x_3576_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3576_, 0, v___x_3571_);
            lean_ctor_set(v___x_3576_, 1, v___x_3572_);
            lean_ctor_set(v___x_3576_, 2, v___x_3574_);
            lean_ctor_set(v___x_3576_, 3, v___x_3575_);
            v___x_3577_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3577_, 0, v___x_3576_);
            lean_ctor_set(v___x_3577_, 1, v_a_3555_);
            return v___x_3577_;
        }
        _ => {
            let mut v_quotContext_3578_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3579_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_3580_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3581_: u8 = 0;
            let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_3578_ = lean_ctor_get(v_a_3554_, 1);
            v_currMacroScope_3579_ = lean_ctor_get(v_a_3554_, 2);
            v_ref_3580_ = lean_ctor_get(v_a_3554_, 5);
            v___x_3581_ = 0;
            v___x_3582_ = l_Lean_SourceInfo_fromRef(v_ref_3580_, v___x_3581_);
            v___x_3583_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16_once
                ),
                _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__16,
            );
            v___x_3584_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__17;
            lean_inc(v_currMacroScope_3579_);
            lean_inc(v_quotContext_3578_);
            v___x_3585_ =
                l_Lean_addMacroScope(v_quotContext_3578_, v___x_3584_, v_currMacroScope_3579_);
            v___x_3586_ =
                l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___closed__21;
            v___x_3587_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3587_, 0, v___x_3582_);
            lean_ctor_set(v___x_3587_, 1, v___x_3583_);
            lean_ctor_set(v___x_3587_, 2, v___x_3585_);
            lean_ctor_set(v___x_3587_, 3, v___x_3586_);
            v___x_3588_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3588_, 0, v___x_3587_);
            lean_ctor_set(v___x_3588_, 1, v_a_3555_);
            return v___x_3588_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ___boxed(
    mut v_x_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4033__boxed_3592_: u8 = 0;
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_x_4033__boxed_3592_ = (lean_unbox(v_x_3589_) as u8);
    v_res_3593_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(
        v_x_4033__boxed_3592_,
        v_a_3590_,
        v_a_3591_,
    );
    lean_dec_ref(v_a_3590_);
    return v_res_3593_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1()
-> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3595_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__0;
    v___x_3596_ = l_String_toRawSubstring_x27(v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10()
-> *mut LeanObject {
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    v___x_3616_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__9;
    v___x_3617_ = l_String_toRawSubstring_x27(v___x_3616_);
    return v___x_3617_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18()
-> *mut LeanObject {
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    v___x_3636_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__17;
    v___x_3637_ = l_String_toRawSubstring_x27(v___x_3636_);
    return v___x_3637_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26()
-> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__25;
    v___x_3657_ = l_String_toRawSubstring_x27(v___x_3656_);
    return v___x_3657_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34()
-> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__33;
    v___x_3677_ = l_String_toRawSubstring_x27(v___x_3676_);
    return v___x_3677_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42()
-> *mut LeanObject {
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    v___x_3696_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__41;
    v___x_3697_ = l_String_toRawSubstring_x27(v___x_3696_);
    return v___x_3697_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57()
-> *mut LeanObject {
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    v___x_3732_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__56;
    v___x_3733_ = l_String_toRawSubstring_x27(v___x_3732_);
    return v___x_3733_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78()
-> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__77;
    v___x_3783_ = l_String_toRawSubstring_x27(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82()
-> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    v___x_3788_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__81;
    v___x_3789_ = l_String_toRawSubstring_x27(v___x_3788_);
    return v___x_3789_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85()
-> *mut LeanObject {
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    v___x_3793_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__84;
    v___x_3794_ = l_String_toRawSubstring_x27(v___x_3793_);
    return v___x_3794_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93()
-> *mut LeanObject {
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    v___x_3813_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__92;
    v___x_3814_ = l_String_toRawSubstring_x27(v___x_3813_);
    return v___x_3814_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101()
-> *mut LeanObject {
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    v___x_3833_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__100;
    v___x_3834_ = l_String_toRawSubstring_x27(v___x_3833_);
    return v___x_3834_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109()
-> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3853_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__108;
    v___x_3854_ = l_String_toRawSubstring_x27(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117()
-> *mut LeanObject {
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    v___x_3873_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__116;
    v___x_3874_ = l_String_toRawSubstring_x27(v___x_3873_);
    return v___x_3874_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125()
-> *mut LeanObject {
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    v___x_3893_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__124;
    v___x_3894_ = l_String_toRawSubstring_x27(v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133()
-> *mut LeanObject {
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3913_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__132;
    v___x_3914_ = l_String_toRawSubstring_x27(v___x_3913_);
    return v___x_3914_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141()
-> *mut LeanObject {
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v___x_3933_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__140;
    v___x_3934_ = l_String_toRawSubstring_x27(v___x_3933_);
    return v___x_3934_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149()
-> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    v___x_3953_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__148;
    v___x_3954_ = l_String_toRawSubstring_x27(v___x_3953_);
    return v___x_3954_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157()
-> *mut LeanObject {
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    v___x_3973_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__156;
    v___x_3974_ = l_String_toRawSubstring_x27(v___x_3973_);
    return v___x_3974_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165()
-> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__164;
    v___x_3994_ = l_String_toRawSubstring_x27(v___x_3993_);
    return v___x_3994_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173()
-> *mut LeanObject {
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4013_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__172;
    v___x_4014_ = l_String_toRawSubstring_x27(v___x_4013_);
    return v___x_4014_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181()
-> *mut LeanObject {
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    v___x_4033_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__180;
    v___x_4034_ = l_String_toRawSubstring_x27(v___x_4033_);
    return v___x_4034_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189()
-> *mut LeanObject {
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    v___x_4053_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__188;
    v___x_4054_ = l_String_toRawSubstring_x27(v___x_4053_);
    return v___x_4054_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197()
-> *mut LeanObject {
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    v___x_4073_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__196;
    v___x_4074_ = l_String_toRawSubstring_x27(v___x_4073_);
    return v___x_4074_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205()
-> *mut LeanObject {
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    v___x_4093_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__204;
    v___x_4094_ = l_String_toRawSubstring_x27(v___x_4093_);
    return v___x_4094_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213()
-> *mut LeanObject {
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v___x_4113_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__212;
    v___x_4114_ = l_String_toRawSubstring_x27(v___x_4113_);
    return v___x_4114_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221()
-> *mut LeanObject {
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    v___x_4133_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__220;
    v___x_4134_ = l_String_toRawSubstring_x27(v___x_4133_);
    return v___x_4134_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229()
-> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__228;
    v___x_4154_ = l_String_toRawSubstring_x27(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237()
-> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4173_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__236;
    v___x_4174_ = l_String_toRawSubstring_x27(v___x_4173_);
    return v___x_4174_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245()
-> *mut LeanObject {
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    v___x_4193_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__244;
    v___x_4194_ = l_String_toRawSubstring_x27(v___x_4193_);
    return v___x_4194_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253()
-> *mut LeanObject {
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    v___x_4213_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__252;
    v___x_4214_ = l_String_toRawSubstring_x27(v___x_4213_);
    return v___x_4214_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261()
-> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    v___x_4233_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__260;
    v___x_4234_ = l_String_toRawSubstring_x27(v___x_4233_);
    return v___x_4234_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269()
-> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    v___x_4253_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__268;
    v___x_4254_ = l_String_toRawSubstring_x27(v___x_4253_);
    return v___x_4254_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(
    mut v_x_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
    mut v_a_4274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_presentation_4275_: u8 = 0;
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4281_: u8 = 0;
    let mut v_quotContext_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v_presentation_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v_quotContext_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v_presentation_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v_quotContext_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_presentation_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v_quotContext_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v_presentation_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4381_: u8 = 0;
    let mut v_quotContext_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_presentation_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v_quotContext_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4451_: u8 = 0;
    let mut v_val_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u8 = 0;
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4459_: u8 = 0;
    let mut v_quotContext_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_presentation_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v_quotContext_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_presentation_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4536_: u8 = 0;
    let mut v_quotContext_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: u8 = 0;
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut v_val_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v_quotContext_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: u8 = 0;
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_presentation_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4639_: u8 = 0;
    let mut v_quotContext_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v_presentation_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v_quotContext_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4682_: u8 = 0;
    let mut v_presentation_4683_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v_quotContext_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: u8 = 0;
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4707_: u8 = 0;
    let mut v_presentation_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v_quotContext_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_val_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v_quotContext_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: u8 = 0;
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4811_: u8 = 0;
    let mut v_presentation_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v_quotContext_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut v_presentation_4837_: u8 = 0;
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v_quotContext_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut v_presentation_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v_quotContext_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4886_: u8 = 0;
    let mut v_presentation_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4893_: u8 = 0;
    let mut v_quotContext_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: u8 = 0;
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut v_presentation_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v_quotContext_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_presentation_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v_quotContext_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_presentation_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v_quotContext_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut v_presentation_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v_quotContext_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut v_presentation_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v_quotContext_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_presentation_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5043_: u8 = 0;
    let mut v_quotContext_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: u8 = 0;
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5061_: u8 = 0;
    let mut v_presentation_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5068_: u8 = 0;
    let mut v_quotContext_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: u8 = 0;
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_presentation_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v_quotContext_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: u8 = 0;
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_quotContext_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_presentation_5123_: u8 = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5129_: u8 = 0;
    let mut v_quotContext_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_presentation_5148_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5154_: u8 = 0;
    let mut v_quotContext_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: u8 = 0;
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_presentation_5173_: u8 = 0;
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v_quotContext_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: u8 = 0;
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_presentation_5198_: u8 = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5204_: u8 = 0;
    let mut v_quotContext_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: u8 = 0;
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_presentation_5223_: u8 = 0;
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v_quotContext_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4272_) {
                0 => {
                    v_presentation_4275_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_4276_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                        v_presentation_4275_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
                    v_a_4278_ = lean_ctor_get(v___x_4276_, 1);
                    v_isSharedCheck_4299_ = (!lean_is_exclusive(v___x_4276_)) as u8;
                    if v_isSharedCheck_4299_ == 0 {
                        v___x_4280_ = v___x_4276_;
                        v_isShared_4281_ = v_isSharedCheck_4299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4278_);
                        lean_inc(v_a_4277_);
                        lean_dec(v___x_4276_);
                        v___x_4280_ = lean_box(0);
                        v_isShared_4281_ = v_isSharedCheck_4299_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_presentation_4300_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4300_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4301_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(
                        v_presentation_4300_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
                    v_a_4303_ = lean_ctor_get(v___x_4301_, 1);
                    v_isSharedCheck_4324_ = (!lean_is_exclusive(v___x_4301_)) as u8;
                    if v_isSharedCheck_4324_ == 0 {
                        v___x_4305_ = v___x_4301_;
                        v_isShared_4306_ = v_isSharedCheck_4324_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4303_);
                        lean_inc(v_a_4302_);
                        lean_dec(v___x_4301_);
                        v___x_4305_ = lean_box(0);
                        v_isShared_4306_ = v_isSharedCheck_4324_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_presentation_4325_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4325_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4326_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(
                        v_presentation_4325_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
                    v_a_4328_ = lean_ctor_get(v___x_4326_, 1);
                    v_isSharedCheck_4349_ = (!lean_is_exclusive(v___x_4326_)) as u8;
                    if v_isSharedCheck_4349_ == 0 {
                        v___x_4330_ = v___x_4326_;
                        v_isShared_4331_ = v_isSharedCheck_4349_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4328_);
                        lean_inc(v_a_4327_);
                        lean_dec(v___x_4326_);
                        v___x_4330_ = lean_box(0);
                        v_isShared_4331_ = v_isSharedCheck_4349_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_presentation_4350_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4350_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4351_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertYear(
                        v_presentation_4350_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
                    v_a_4353_ = lean_ctor_get(v___x_4351_, 1);
                    v_isSharedCheck_4374_ = (!lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4374_ == 0 {
                        v___x_4355_ = v___x_4351_;
                        v_isShared_4356_ = v_isSharedCheck_4374_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4353_);
                        lean_inc(v_a_4352_);
                        lean_dec(v___x_4351_);
                        v___x_4355_ = lean_box(0);
                        v_isShared_4356_ = v_isSharedCheck_4374_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_presentation_4375_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4375_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4376_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4375_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
                    v_a_4378_ = lean_ctor_get(v___x_4376_, 1);
                    v_isSharedCheck_4399_ = (!lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4399_ == 0 {
                        v___x_4380_ = v___x_4376_;
                        v_isShared_4381_ = v_isSharedCheck_4399_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4378_);
                        lean_inc(v_a_4377_);
                        lean_dec(v___x_4376_);
                        v___x_4380_ = lean_box(0);
                        v_isShared_4381_ = v_isSharedCheck_4399_;
                        state = 9;
                        continue;
                    }
                }
                5 => {
                    v_presentation_4400_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc_ref(v_presentation_4400_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    if lean_obj_tag(v_presentation_4400_) == 0 {
                        v_val_4401_ = lean_ctor_get(v_presentation_4400_, 0);
                        lean_inc(v_val_4401_);
                        lean_dec_ref_known(v_presentation_4400_, 1);
                        v___x_4402_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                            v_val_4401_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
                        v_a_4404_ = lean_ctor_get(v___x_4402_, 1);
                        v_isSharedCheck_4451_ = (!lean_is_exclusive(v___x_4402_)) as u8;
                        if v_isSharedCheck_4451_ == 0 {
                            v___x_4406_ = v___x_4402_;
                            v_isShared_4407_ = v_isSharedCheck_4451_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4404_);
                            lean_inc(v_a_4403_);
                            lean_dec(v___x_4402_);
                            v___x_4406_ = lean_box(0);
                            v_isShared_4407_ = v_isSharedCheck_4451_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_val_4452_ = lean_ctor_get(v_presentation_4400_, 0);
                        lean_inc(v_val_4452_);
                        lean_dec_ref_known(v_presentation_4400_, 1);
                        v___x_4453_ = (lean_unbox(v_val_4452_) as u8);
                        lean_dec(v_val_4452_);
                        v___x_4454_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                            v___x_4453_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
                        v_a_4456_ = lean_ctor_get(v___x_4454_, 1);
                        v_isSharedCheck_4503_ = (!lean_is_exclusive(v___x_4454_)) as u8;
                        if v_isSharedCheck_4503_ == 0 {
                            v___x_4458_ = v___x_4454_;
                            v_isShared_4459_ = v_isSharedCheck_4503_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4456_);
                            lean_inc(v_a_4455_);
                            lean_dec(v___x_4454_);
                            v___x_4458_ = lean_box(0);
                            v_isShared_4459_ = v_isSharedCheck_4503_;
                            state = 13;
                            continue;
                        }
                    }
                }
                6 => {
                    v_presentation_4504_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4504_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4505_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4504_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
                    v_a_4507_ = lean_ctor_get(v___x_4505_, 1);
                    v_isSharedCheck_4528_ = (!lean_is_exclusive(v___x_4505_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4509_ = v___x_4505_;
                        v_isShared_4510_ = v_isSharedCheck_4528_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4507_);
                        lean_inc(v_a_4506_);
                        lean_dec(v___x_4505_);
                        v___x_4509_ = lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4528_;
                        state = 15;
                        continue;
                    }
                }
                7 => {
                    v_presentation_4529_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc_ref(v_presentation_4529_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    if lean_obj_tag(v_presentation_4529_) == 0 {
                        v_val_4530_ = lean_ctor_get(v_presentation_4529_, 0);
                        lean_inc(v_val_4530_);
                        lean_dec_ref_known(v_presentation_4529_, 1);
                        v___x_4531_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                            v_val_4530_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
                        v_a_4533_ = lean_ctor_get(v___x_4531_, 1);
                        v_isSharedCheck_4580_ = (!lean_is_exclusive(v___x_4531_)) as u8;
                        if v_isSharedCheck_4580_ == 0 {
                            v___x_4535_ = v___x_4531_;
                            v_isShared_4536_ = v_isSharedCheck_4580_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_4533_);
                            lean_inc(v_a_4532_);
                            lean_dec(v___x_4531_);
                            v___x_4535_ = lean_box(0);
                            v_isShared_4536_ = v_isSharedCheck_4580_;
                            state = 17;
                            continue;
                        }
                    } else {
                        v_val_4581_ = lean_ctor_get(v_presentation_4529_, 0);
                        lean_inc(v_val_4581_);
                        lean_dec_ref_known(v_presentation_4529_, 1);
                        v___x_4582_ = (lean_unbox(v_val_4581_) as u8);
                        lean_dec(v_val_4581_);
                        v___x_4583_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                            v___x_4582_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
                        v_a_4585_ = lean_ctor_get(v___x_4583_, 1);
                        v_isSharedCheck_4632_ = (!lean_is_exclusive(v___x_4583_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4587_ = v___x_4583_;
                            v_isShared_4588_ = v_isSharedCheck_4632_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_4585_);
                            lean_inc(v_a_4584_);
                            lean_dec(v___x_4583_);
                            v___x_4587_ = lean_box(0);
                            v_isShared_4588_ = v_isSharedCheck_4632_;
                            state = 19;
                            continue;
                        }
                    }
                }
                8 => {
                    v_presentation_4633_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4633_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4634_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4633_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
                    v_a_4636_ = lean_ctor_get(v___x_4634_, 1);
                    v_isSharedCheck_4657_ = (!lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4638_ = v___x_4634_;
                        v_isShared_4639_ = v_isSharedCheck_4657_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_4636_);
                        lean_inc(v_a_4635_);
                        lean_dec(v___x_4634_);
                        v___x_4638_ = lean_box(0);
                        v_isShared_4639_ = v_isSharedCheck_4657_;
                        state = 21;
                        continue;
                    }
                }
                9 => {
                    v_presentation_4658_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4658_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4659_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4658_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
                    v_a_4661_ = lean_ctor_get(v___x_4659_, 1);
                    v_isSharedCheck_4682_ = (!lean_is_exclusive(v___x_4659_)) as u8;
                    if v_isSharedCheck_4682_ == 0 {
                        v___x_4663_ = v___x_4659_;
                        v_isShared_4664_ = v_isSharedCheck_4682_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4661_);
                        lean_inc(v_a_4660_);
                        lean_dec(v___x_4659_);
                        v___x_4663_ = lean_box(0);
                        v_isShared_4664_ = v_isSharedCheck_4682_;
                        state = 23;
                        continue;
                    }
                }
                10 => {
                    v_presentation_4683_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_4684_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                        v_presentation_4683_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
                    v_a_4686_ = lean_ctor_get(v___x_4684_, 1);
                    v_isSharedCheck_4707_ = (!lean_is_exclusive(v___x_4684_)) as u8;
                    if v_isSharedCheck_4707_ == 0 {
                        v___x_4688_ = v___x_4684_;
                        v_isShared_4689_ = v_isSharedCheck_4707_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_4686_);
                        lean_inc(v_a_4685_);
                        lean_dec(v___x_4684_);
                        v___x_4688_ = lean_box(0);
                        v_isShared_4689_ = v_isSharedCheck_4707_;
                        state = 25;
                        continue;
                    }
                }
                11 => {
                    v_presentation_4708_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc_ref(v_presentation_4708_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    if lean_obj_tag(v_presentation_4708_) == 0 {
                        v_val_4709_ = lean_ctor_get(v_presentation_4708_, 0);
                        lean_inc(v_val_4709_);
                        lean_dec_ref_known(v_presentation_4708_, 1);
                        v___x_4710_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                            v_val_4709_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
                        v_a_4712_ = lean_ctor_get(v___x_4710_, 1);
                        v_isSharedCheck_4759_ = (!lean_is_exclusive(v___x_4710_)) as u8;
                        if v_isSharedCheck_4759_ == 0 {
                            v___x_4714_ = v___x_4710_;
                            v_isShared_4715_ = v_isSharedCheck_4759_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_4712_);
                            lean_inc(v_a_4711_);
                            lean_dec(v___x_4710_);
                            v___x_4714_ = lean_box(0);
                            v_isShared_4715_ = v_isSharedCheck_4759_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_val_4760_ = lean_ctor_get(v_presentation_4708_, 0);
                        lean_inc(v_val_4760_);
                        lean_dec_ref_known(v_presentation_4708_, 1);
                        v___x_4761_ = (lean_unbox(v_val_4760_) as u8);
                        lean_dec(v_val_4760_);
                        v___x_4762_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                            v___x_4761_,
                            v_a_4273_,
                            v_a_4274_,
                        );
                        v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
                        v_a_4764_ = lean_ctor_get(v___x_4762_, 1);
                        v_isSharedCheck_4811_ = (!lean_is_exclusive(v___x_4762_)) as u8;
                        if v_isSharedCheck_4811_ == 0 {
                            v___x_4766_ = v___x_4762_;
                            v_isShared_4767_ = v_isSharedCheck_4811_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_4764_);
                            lean_inc(v_a_4763_);
                            lean_dec(v___x_4762_);
                            v___x_4766_ = lean_box(0);
                            v_isShared_4767_ = v_isSharedCheck_4811_;
                            state = 29;
                            continue;
                        }
                    }
                }
                12 => {
                    v_presentation_4812_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4812_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4813_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4812_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
                    v_a_4815_ = lean_ctor_get(v___x_4813_, 1);
                    v_isSharedCheck_4836_ = (!lean_is_exclusive(v___x_4813_)) as u8;
                    if v_isSharedCheck_4836_ == 0 {
                        v___x_4817_ = v___x_4813_;
                        v_isShared_4818_ = v_isSharedCheck_4836_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_4815_);
                        lean_inc(v_a_4814_);
                        lean_dec(v___x_4813_);
                        v___x_4817_ = lean_box(0);
                        v_isShared_4818_ = v_isSharedCheck_4836_;
                        state = 31;
                        continue;
                    }
                }
                13 => {
                    v_presentation_4837_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_4838_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertText(
                        v_presentation_4837_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
                    v_a_4840_ = lean_ctor_get(v___x_4838_, 1);
                    v_isSharedCheck_4861_ = (!lean_is_exclusive(v___x_4838_)) as u8;
                    if v_isSharedCheck_4861_ == 0 {
                        v___x_4842_ = v___x_4838_;
                        v_isShared_4843_ = v_isSharedCheck_4861_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_4840_);
                        lean_inc(v_a_4839_);
                        lean_dec(v___x_4838_);
                        v___x_4842_ = lean_box(0);
                        v_isShared_4843_ = v_isSharedCheck_4861_;
                        state = 33;
                        continue;
                    }
                }
                14 => {
                    v_presentation_4862_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4862_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4863_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4862_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
                    v_a_4865_ = lean_ctor_get(v___x_4863_, 1);
                    v_isSharedCheck_4886_ = (!lean_is_exclusive(v___x_4863_)) as u8;
                    if v_isSharedCheck_4886_ == 0 {
                        v___x_4867_ = v___x_4863_;
                        v_isShared_4868_ = v_isSharedCheck_4886_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_4865_);
                        lean_inc(v_a_4864_);
                        lean_dec(v___x_4863_);
                        v___x_4867_ = lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4886_;
                        state = 35;
                        continue;
                    }
                }
                15 => {
                    v_presentation_4887_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4887_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4888_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4887_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
                    v_a_4890_ = lean_ctor_get(v___x_4888_, 1);
                    v_isSharedCheck_4911_ = (!lean_is_exclusive(v___x_4888_)) as u8;
                    if v_isSharedCheck_4911_ == 0 {
                        v___x_4892_ = v___x_4888_;
                        v_isShared_4893_ = v_isSharedCheck_4911_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_4890_);
                        lean_inc(v_a_4889_);
                        lean_dec(v___x_4888_);
                        v___x_4892_ = lean_box(0);
                        v_isShared_4893_ = v_isSharedCheck_4911_;
                        state = 37;
                        continue;
                    }
                }
                16 => {
                    v_presentation_4912_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4912_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4913_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4912_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
                    v_a_4915_ = lean_ctor_get(v___x_4913_, 1);
                    v_isSharedCheck_4936_ = (!lean_is_exclusive(v___x_4913_)) as u8;
                    if v_isSharedCheck_4936_ == 0 {
                        v___x_4917_ = v___x_4913_;
                        v_isShared_4918_ = v_isSharedCheck_4936_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_4915_);
                        lean_inc(v_a_4914_);
                        lean_dec(v___x_4913_);
                        v___x_4917_ = lean_box(0);
                        v_isShared_4918_ = v_isSharedCheck_4936_;
                        state = 39;
                        continue;
                    }
                }
                17 => {
                    v_presentation_4937_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4937_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4938_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4937_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
                    v_a_4940_ = lean_ctor_get(v___x_4938_, 1);
                    v_isSharedCheck_4961_ = (!lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v___x_4942_ = v___x_4938_;
                        v_isShared_4943_ = v_isSharedCheck_4961_;
                        state = 41;
                        continue;
                    } else {
                        lean_inc(v_a_4940_);
                        lean_inc(v_a_4939_);
                        lean_dec(v___x_4938_);
                        v___x_4942_ = lean_box(0);
                        v_isShared_4943_ = v_isSharedCheck_4961_;
                        state = 41;
                        continue;
                    }
                }
                18 => {
                    v_presentation_4962_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4962_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4963_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4962_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
                    v_a_4965_ = lean_ctor_get(v___x_4963_, 1);
                    v_isSharedCheck_4986_ = (!lean_is_exclusive(v___x_4963_)) as u8;
                    if v_isSharedCheck_4986_ == 0 {
                        v___x_4967_ = v___x_4963_;
                        v_isShared_4968_ = v_isSharedCheck_4986_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_4965_);
                        lean_inc(v_a_4964_);
                        lean_dec(v___x_4963_);
                        v___x_4967_ = lean_box(0);
                        v_isShared_4968_ = v_isSharedCheck_4986_;
                        state = 43;
                        continue;
                    }
                }
                19 => {
                    v_presentation_4987_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_4987_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_4988_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_4987_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
                    v_a_4990_ = lean_ctor_get(v___x_4988_, 1);
                    v_isSharedCheck_5011_ = (!lean_is_exclusive(v___x_4988_)) as u8;
                    if v_isSharedCheck_5011_ == 0 {
                        v___x_4992_ = v___x_4988_;
                        v_isShared_4993_ = v_isSharedCheck_5011_;
                        state = 45;
                        continue;
                    } else {
                        lean_inc(v_a_4990_);
                        lean_inc(v_a_4989_);
                        lean_dec(v___x_4988_);
                        v___x_4992_ = lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_5011_;
                        state = 45;
                        continue;
                    }
                }
                20 => {
                    v_presentation_5012_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_5012_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_5013_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFraction(
                        v_presentation_5012_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
                    v_a_5015_ = lean_ctor_get(v___x_5013_, 1);
                    v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5013_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5017_ = v___x_5013_;
                        v_isShared_5018_ = v_isSharedCheck_5036_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_a_5015_);
                        lean_inc(v_a_5014_);
                        lean_dec(v___x_5013_);
                        v___x_5017_ = lean_box(0);
                        v_isShared_5018_ = v_isSharedCheck_5036_;
                        state = 47;
                        continue;
                    }
                }
                21 => {
                    v_presentation_5037_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_5037_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_5038_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_5037_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
                    v_a_5040_ = lean_ctor_get(v___x_5038_, 1);
                    v_isSharedCheck_5061_ = (!lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5061_ == 0 {
                        v___x_5042_ = v___x_5038_;
                        v_isShared_5043_ = v_isSharedCheck_5061_;
                        state = 49;
                        continue;
                    } else {
                        lean_inc(v_a_5040_);
                        lean_inc(v_a_5039_);
                        lean_dec(v___x_5038_);
                        v___x_5042_ = lean_box(0);
                        v_isShared_5043_ = v_isSharedCheck_5061_;
                        state = 49;
                        continue;
                    }
                }
                22 => {
                    v_presentation_5062_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_5062_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_5063_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_5062_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
                    v_a_5065_ = lean_ctor_get(v___x_5063_, 1);
                    v_isSharedCheck_5086_ = (!lean_is_exclusive(v___x_5063_)) as u8;
                    if v_isSharedCheck_5086_ == 0 {
                        v___x_5067_ = v___x_5063_;
                        v_isShared_5068_ = v_isSharedCheck_5086_;
                        state = 51;
                        continue;
                    } else {
                        lean_inc(v_a_5065_);
                        lean_inc(v_a_5064_);
                        lean_dec(v___x_5063_);
                        v___x_5067_ = lean_box(0);
                        v_isShared_5068_ = v_isSharedCheck_5086_;
                        state = 51;
                        continue;
                    }
                }
                23 => {
                    v_presentation_5087_ = lean_ctor_get(v_x_4272_, 0);
                    lean_inc(v_presentation_5087_);
                    lean_dec_ref_known(v_x_4272_, 1);
                    v___x_5088_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber(
                        v_presentation_5087_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
                    v_a_5090_ = lean_ctor_get(v___x_5088_, 1);
                    v_isSharedCheck_5111_ = (!lean_is_exclusive(v___x_5088_)) as u8;
                    if v_isSharedCheck_5111_ == 0 {
                        v___x_5092_ = v___x_5088_;
                        v_isShared_5093_ = v_isSharedCheck_5111_;
                        state = 53;
                        continue;
                    } else {
                        lean_inc(v_a_5090_);
                        lean_inc(v_a_5089_);
                        lean_dec(v___x_5088_);
                        v___x_5092_ = lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5111_;
                        state = 53;
                        continue;
                    }
                }
                24 => {
                    v_quotContext_5112_ = lean_ctor_get(v_a_4273_, 1);
                    v_currMacroScope_5113_ = lean_ctor_get(v_a_4273_, 2);
                    v_ref_5114_ = lean_ctor_get(v_a_4273_, 5);
                    v___x_5115_ = 0;
                    v___x_5116_ = l_Lean_SourceInfo_fromRef(v_ref_5114_, v___x_5115_);
                    v___x_5117_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__229);
                    v___x_5118_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__231;
                    lean_inc(v_currMacroScope_5113_);
                    lean_inc(v_quotContext_5112_);
                    v___x_5119_ = l_Lean_addMacroScope(
                        v_quotContext_5112_,
                        v___x_5118_,
                        v_currMacroScope_5113_,
                    );
                    v___x_5120_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__235;
                    v___x_5121_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5121_, 0, v___x_5116_);
                    lean_ctor_set(v___x_5121_, 1, v___x_5117_);
                    lean_ctor_set(v___x_5121_, 2, v___x_5119_);
                    lean_ctor_set(v___x_5121_, 3, v___x_5120_);
                    v___x_5122_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5122_, 0, v___x_5121_);
                    lean_ctor_set(v___x_5122_, 1, v_a_4274_);
                    return v___x_5122_;
                }
                25 => {
                    v_presentation_5123_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_5124_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertZoneName(
                        v_presentation_5123_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
                    v_a_5126_ = lean_ctor_get(v___x_5124_, 1);
                    v_isSharedCheck_5147_ = (!lean_is_exclusive(v___x_5124_)) as u8;
                    if v_isSharedCheck_5147_ == 0 {
                        v___x_5128_ = v___x_5124_;
                        v_isShared_5129_ = v_isSharedCheck_5147_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_a_5126_);
                        lean_inc(v_a_5125_);
                        lean_dec(v___x_5124_);
                        v___x_5128_ = lean_box(0);
                        v_isShared_5129_ = v_isSharedCheck_5147_;
                        state = 55;
                        continue;
                    }
                }
                26 => {
                    v_presentation_5148_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_5149_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetO(
                        v_presentation_5148_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
                    v_a_5151_ = lean_ctor_get(v___x_5149_, 1);
                    v_isSharedCheck_5172_ = (!lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5172_ == 0 {
                        v___x_5153_ = v___x_5149_;
                        v_isShared_5154_ = v_isSharedCheck_5172_;
                        state = 57;
                        continue;
                    } else {
                        lean_inc(v_a_5151_);
                        lean_inc(v_a_5150_);
                        lean_dec(v___x_5149_);
                        v___x_5153_ = lean_box(0);
                        v_isShared_5154_ = v_isSharedCheck_5172_;
                        state = 57;
                        continue;
                    }
                }
                27 => {
                    v_presentation_5173_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_5174_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(
                        v_presentation_5173_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
                    v_a_5176_ = lean_ctor_get(v___x_5174_, 1);
                    v_isSharedCheck_5197_ = (!lean_is_exclusive(v___x_5174_)) as u8;
                    if v_isSharedCheck_5197_ == 0 {
                        v___x_5178_ = v___x_5174_;
                        v_isShared_5179_ = v_isSharedCheck_5197_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_a_5176_);
                        lean_inc(v_a_5175_);
                        lean_dec(v___x_5174_);
                        v___x_5178_ = lean_box(0);
                        v_isShared_5179_ = v_isSharedCheck_5197_;
                        state = 59;
                        continue;
                    }
                }
                28 => {
                    v_presentation_5198_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_5199_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetX(
                        v_presentation_5198_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
                    v_a_5201_ = lean_ctor_get(v___x_5199_, 1);
                    v_isSharedCheck_5222_ = (!lean_is_exclusive(v___x_5199_)) as u8;
                    if v_isSharedCheck_5222_ == 0 {
                        v___x_5203_ = v___x_5199_;
                        v_isShared_5204_ = v_isSharedCheck_5222_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_a_5201_);
                        lean_inc(v_a_5200_);
                        lean_dec(v___x_5199_);
                        v___x_5203_ = lean_box(0);
                        v_isShared_5204_ = v_isSharedCheck_5222_;
                        state = 61;
                        continue;
                    }
                }
                _ => {
                    v_presentation_5223_ = lean_ctor_get_uint8(v_x_4272_, 0 as u32);
                    lean_dec_ref_known(v_x_4272_, 0);
                    v___x_5224_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertOffsetZ(
                        v_presentation_5223_,
                        v_a_4273_,
                        v_a_4274_,
                    );
                    v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
                    v_a_5226_ = lean_ctor_get(v___x_5224_, 1);
                    v_isSharedCheck_5247_ = (!lean_is_exclusive(v___x_5224_)) as u8;
                    if v_isSharedCheck_5247_ == 0 {
                        v___x_5228_ = v___x_5224_;
                        v_isShared_5229_ = v_isSharedCheck_5247_;
                        state = 63;
                        continue;
                    } else {
                        lean_inc(v_a_5226_);
                        lean_inc(v_a_5225_);
                        lean_dec(v___x_5224_);
                        v___x_5228_ = lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5247_;
                        state = 63;
                        continue;
                    }
                }
            },
            1 => {
                v_quotContext_4282_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4283_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4284_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4285_ = 0;
                v___x_4286_ = l_Lean_SourceInfo_fromRef(v_ref_4284_, v___x_4285_);
                v___x_4287_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4288_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__1);
                v___x_4289_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__4;
                lean_inc(v_currMacroScope_4283_);
                lean_inc(v_quotContext_4282_);
                v___x_4290_ =
                    l_Lean_addMacroScope(v_quotContext_4282_, v___x_4289_, v_currMacroScope_4283_);
                v___x_4291_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__8;
                lean_inc_n(v___x_4286_, 2);
                v___x_4292_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4292_, 0, v___x_4286_);
                lean_ctor_set(v___x_4292_, 1, v___x_4288_);
                lean_ctor_set(v___x_4292_, 2, v___x_4290_);
                lean_ctor_set(v___x_4292_, 3, v___x_4291_);
                v___x_4293_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4294_ = l_Lean_Syntax_node1(v___x_4286_, v___x_4293_, v_a_4277_);
                v___x_4295_ =
                    l_Lean_Syntax_node2(v___x_4286_, v___x_4287_, v___x_4292_, v___x_4294_);
                if v_isShared_4281_ == 0 {
                    lean_ctor_set(v___x_4280_, 0, v___x_4295_);
                    v___x_4297_ = v___x_4280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_a_4278_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4297_;
            }
            3 => {
                v_quotContext_4307_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4308_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4309_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4310_ = 0;
                v___x_4311_ = l_Lean_SourceInfo_fromRef(v_ref_4309_, v___x_4310_);
                v___x_4312_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4313_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__10);
                v___x_4314_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__12;
                lean_inc(v_currMacroScope_4308_);
                lean_inc(v_quotContext_4307_);
                v___x_4315_ =
                    l_Lean_addMacroScope(v_quotContext_4307_, v___x_4314_, v_currMacroScope_4308_);
                v___x_4316_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__16;
                lean_inc_n(v___x_4311_, 2);
                v___x_4317_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4317_, 0, v___x_4311_);
                lean_ctor_set(v___x_4317_, 1, v___x_4313_);
                lean_ctor_set(v___x_4317_, 2, v___x_4315_);
                lean_ctor_set(v___x_4317_, 3, v___x_4316_);
                v___x_4318_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4319_ = l_Lean_Syntax_node1(v___x_4311_, v___x_4318_, v_a_4302_);
                v___x_4320_ =
                    l_Lean_Syntax_node2(v___x_4311_, v___x_4312_, v___x_4317_, v___x_4319_);
                if v_isShared_4306_ == 0 {
                    lean_ctor_set(v___x_4305_, 0, v___x_4320_);
                    v___x_4322_ = v___x_4305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
                    lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_a_4303_);
                    v___x_4322_ = v_reuseFailAlloc_4323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4322_;
            }
            5 => {
                v_quotContext_4332_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4333_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4334_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4335_ = 0;
                v___x_4336_ = l_Lean_SourceInfo_fromRef(v_ref_4334_, v___x_4335_);
                v___x_4337_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4338_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__18);
                v___x_4339_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__20;
                lean_inc(v_currMacroScope_4333_);
                lean_inc(v_quotContext_4332_);
                v___x_4340_ =
                    l_Lean_addMacroScope(v_quotContext_4332_, v___x_4339_, v_currMacroScope_4333_);
                v___x_4341_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__24;
                lean_inc_n(v___x_4336_, 2);
                v___x_4342_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4342_, 0, v___x_4336_);
                lean_ctor_set(v___x_4342_, 1, v___x_4338_);
                lean_ctor_set(v___x_4342_, 2, v___x_4340_);
                lean_ctor_set(v___x_4342_, 3, v___x_4341_);
                v___x_4343_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4344_ = l_Lean_Syntax_node1(v___x_4336_, v___x_4343_, v_a_4327_);
                v___x_4345_ =
                    l_Lean_Syntax_node2(v___x_4336_, v___x_4337_, v___x_4342_, v___x_4344_);
                if v_isShared_4331_ == 0 {
                    lean_ctor_set(v___x_4330_, 0, v___x_4345_);
                    v___x_4347_ = v___x_4330_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
                    lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_a_4328_);
                    v___x_4347_ = v_reuseFailAlloc_4348_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4347_;
            }
            7 => {
                v_quotContext_4357_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4358_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4359_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4360_ = 0;
                v___x_4361_ = l_Lean_SourceInfo_fromRef(v_ref_4359_, v___x_4360_);
                v___x_4362_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4363_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__26);
                v___x_4364_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__28;
                lean_inc(v_currMacroScope_4358_);
                lean_inc(v_quotContext_4357_);
                v___x_4365_ =
                    l_Lean_addMacroScope(v_quotContext_4357_, v___x_4364_, v_currMacroScope_4358_);
                v___x_4366_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__32;
                lean_inc_n(v___x_4361_, 2);
                v___x_4367_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4367_, 0, v___x_4361_);
                lean_ctor_set(v___x_4367_, 1, v___x_4363_);
                lean_ctor_set(v___x_4367_, 2, v___x_4365_);
                lean_ctor_set(v___x_4367_, 3, v___x_4366_);
                v___x_4368_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4369_ = l_Lean_Syntax_node1(v___x_4361_, v___x_4368_, v_a_4352_);
                v___x_4370_ =
                    l_Lean_Syntax_node2(v___x_4361_, v___x_4362_, v___x_4367_, v___x_4369_);
                if v_isShared_4356_ == 0 {
                    lean_ctor_set(v___x_4355_, 0, v___x_4370_);
                    v___x_4372_ = v___x_4355_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
                    lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_a_4353_);
                    v___x_4372_ = v_reuseFailAlloc_4373_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4372_;
            }
            9 => {
                v_quotContext_4382_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4383_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4384_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4385_ = 0;
                v___x_4386_ = l_Lean_SourceInfo_fromRef(v_ref_4384_, v___x_4385_);
                v___x_4387_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4388_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__34);
                v___x_4389_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__36;
                lean_inc(v_currMacroScope_4383_);
                lean_inc(v_quotContext_4382_);
                v___x_4390_ =
                    l_Lean_addMacroScope(v_quotContext_4382_, v___x_4389_, v_currMacroScope_4383_);
                v___x_4391_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__40;
                lean_inc_n(v___x_4386_, 2);
                v___x_4392_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4392_, 0, v___x_4386_);
                lean_ctor_set(v___x_4392_, 1, v___x_4388_);
                lean_ctor_set(v___x_4392_, 2, v___x_4390_);
                lean_ctor_set(v___x_4392_, 3, v___x_4391_);
                v___x_4393_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4394_ = l_Lean_Syntax_node1(v___x_4386_, v___x_4393_, v_a_4377_);
                v___x_4395_ =
                    l_Lean_Syntax_node2(v___x_4386_, v___x_4387_, v___x_4392_, v___x_4394_);
                if v_isShared_4381_ == 0 {
                    lean_ctor_set(v___x_4380_, 0, v___x_4395_);
                    v___x_4397_ = v___x_4380_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
                    lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4378_);
                    v___x_4397_ = v_reuseFailAlloc_4398_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4397_;
            }
            11 => {
                v_quotContext_4408_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4409_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4410_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4411_ = 0;
                v___x_4412_ = l_Lean_SourceInfo_fromRef(v_ref_4410_, v___x_4411_);
                v___x_4413_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4414_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42);
                v___x_4415_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44;
                lean_inc_n(v_currMacroScope_4409_, 3);
                lean_inc_n(v_quotContext_4408_, 3);
                v___x_4416_ =
                    l_Lean_addMacroScope(v_quotContext_4408_, v___x_4415_, v_currMacroScope_4409_);
                v___x_4417_ = lean_box(0);
                v___x_4418_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48;
                lean_inc_n(v___x_4412_, 13);
                v___x_4419_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4419_, 0, v___x_4412_);
                lean_ctor_set(v___x_4419_, 1, v___x_4414_);
                lean_ctor_set(v___x_4419_, 2, v___x_4416_);
                lean_ctor_set(v___x_4419_, 3, v___x_4418_);
                v___x_4420_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4421_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4422_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4423_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4424_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4424_, 0, v___x_4412_);
                lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                v___x_4425_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4426_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4427_ = lean_box(0);
                v___x_4428_ =
                    l_Lean_addMacroScope(v_quotContext_4408_, v___x_4427_, v_currMacroScope_4409_);
                v___x_4429_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4430_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4430_, 0, v___x_4412_);
                lean_ctor_set(v___x_4430_, 1, v___x_4426_);
                lean_ctor_set(v___x_4430_, 2, v___x_4428_);
                lean_ctor_set(v___x_4430_, 3, v___x_4429_);
                v___x_4431_ = l_Lean_Syntax_node1(v___x_4412_, v___x_4425_, v___x_4430_);
                v___x_4432_ =
                    l_Lean_Syntax_node2(v___x_4412_, v___x_4422_, v___x_4424_, v___x_4431_);
                v___x_4433_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4434_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4435_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4435_, 0, v___x_4412_);
                lean_ctor_set(v___x_4435_, 1, v___x_4434_);
                v___x_4436_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78);
                v___x_4437_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79;
                v___x_4438_ =
                    l_Lean_addMacroScope(v_quotContext_4408_, v___x_4437_, v_currMacroScope_4409_);
                v___x_4439_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4439_, 0, v___x_4412_);
                lean_ctor_set(v___x_4439_, 1, v___x_4436_);
                lean_ctor_set(v___x_4439_, 2, v___x_4438_);
                lean_ctor_set(v___x_4439_, 3, v___x_4417_);
                v___x_4440_ =
                    l_Lean_Syntax_node2(v___x_4412_, v___x_4433_, v___x_4435_, v___x_4439_);
                v___x_4441_ = l_Lean_Syntax_node1(v___x_4412_, v___x_4420_, v_a_4403_);
                v___x_4442_ =
                    l_Lean_Syntax_node2(v___x_4412_, v___x_4413_, v___x_4440_, v___x_4441_);
                v___x_4443_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4444_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4444_, 0, v___x_4412_);
                lean_ctor_set(v___x_4444_, 1, v___x_4443_);
                v___x_4445_ = l_Lean_Syntax_node3(
                    v___x_4412_,
                    v___x_4421_,
                    v___x_4432_,
                    v___x_4442_,
                    v___x_4444_,
                );
                v___x_4446_ = l_Lean_Syntax_node1(v___x_4412_, v___x_4420_, v___x_4445_);
                v___x_4447_ =
                    l_Lean_Syntax_node2(v___x_4412_, v___x_4413_, v___x_4419_, v___x_4446_);
                if v_isShared_4407_ == 0 {
                    lean_ctor_set(v___x_4406_, 0, v___x_4447_);
                    v___x_4449_ = v___x_4406_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
                    lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_a_4404_);
                    v___x_4449_ = v_reuseFailAlloc_4450_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4449_;
            }
            13 => {
                v_quotContext_4460_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4461_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4462_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4463_ = 0;
                v___x_4464_ = l_Lean_SourceInfo_fromRef(v_ref_4462_, v___x_4463_);
                v___x_4465_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4466_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__42);
                v___x_4467_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__44;
                lean_inc_n(v_currMacroScope_4461_, 3);
                lean_inc_n(v_quotContext_4460_, 3);
                v___x_4468_ =
                    l_Lean_addMacroScope(v_quotContext_4460_, v___x_4467_, v_currMacroScope_4461_);
                v___x_4469_ = lean_box(0);
                v___x_4470_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__48;
                lean_inc_n(v___x_4464_, 13);
                v___x_4471_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4471_, 0, v___x_4464_);
                lean_ctor_set(v___x_4471_, 1, v___x_4466_);
                lean_ctor_set(v___x_4471_, 2, v___x_4468_);
                lean_ctor_set(v___x_4471_, 3, v___x_4470_);
                v___x_4472_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4473_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4474_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4475_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4476_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4476_, 0, v___x_4464_);
                lean_ctor_set(v___x_4476_, 1, v___x_4475_);
                v___x_4477_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4478_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4479_ = lean_box(0);
                v___x_4480_ =
                    l_Lean_addMacroScope(v_quotContext_4460_, v___x_4479_, v_currMacroScope_4461_);
                v___x_4481_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4482_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4482_, 0, v___x_4464_);
                lean_ctor_set(v___x_4482_, 1, v___x_4478_);
                lean_ctor_set(v___x_4482_, 2, v___x_4480_);
                lean_ctor_set(v___x_4482_, 3, v___x_4481_);
                v___x_4483_ = l_Lean_Syntax_node1(v___x_4464_, v___x_4477_, v___x_4482_);
                v___x_4484_ =
                    l_Lean_Syntax_node2(v___x_4464_, v___x_4474_, v___x_4476_, v___x_4483_);
                v___x_4485_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4486_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4487_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4487_, 0, v___x_4464_);
                lean_ctor_set(v___x_4487_, 1, v___x_4486_);
                v___x_4488_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82);
                v___x_4489_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83;
                v___x_4490_ =
                    l_Lean_addMacroScope(v_quotContext_4460_, v___x_4489_, v_currMacroScope_4461_);
                v___x_4491_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4491_, 0, v___x_4464_);
                lean_ctor_set(v___x_4491_, 1, v___x_4488_);
                lean_ctor_set(v___x_4491_, 2, v___x_4490_);
                lean_ctor_set(v___x_4491_, 3, v___x_4469_);
                v___x_4492_ =
                    l_Lean_Syntax_node2(v___x_4464_, v___x_4485_, v___x_4487_, v___x_4491_);
                v___x_4493_ = l_Lean_Syntax_node1(v___x_4464_, v___x_4472_, v_a_4455_);
                v___x_4494_ =
                    l_Lean_Syntax_node2(v___x_4464_, v___x_4465_, v___x_4492_, v___x_4493_);
                v___x_4495_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4496_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4496_, 0, v___x_4464_);
                lean_ctor_set(v___x_4496_, 1, v___x_4495_);
                v___x_4497_ = l_Lean_Syntax_node3(
                    v___x_4464_,
                    v___x_4473_,
                    v___x_4484_,
                    v___x_4494_,
                    v___x_4496_,
                );
                v___x_4498_ = l_Lean_Syntax_node1(v___x_4464_, v___x_4472_, v___x_4497_);
                v___x_4499_ =
                    l_Lean_Syntax_node2(v___x_4464_, v___x_4465_, v___x_4471_, v___x_4498_);
                if v_isShared_4459_ == 0 {
                    lean_ctor_set(v___x_4458_, 0, v___x_4499_);
                    v___x_4501_ = v___x_4458_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_a_4456_);
                    v___x_4501_ = v_reuseFailAlloc_4502_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4501_;
            }
            15 => {
                v_quotContext_4511_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4512_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4513_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4514_ = 0;
                v___x_4515_ = l_Lean_SourceInfo_fromRef(v_ref_4513_, v___x_4514_);
                v___x_4516_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4517_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__85);
                v___x_4518_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__87;
                lean_inc(v_currMacroScope_4512_);
                lean_inc(v_quotContext_4511_);
                v___x_4519_ =
                    l_Lean_addMacroScope(v_quotContext_4511_, v___x_4518_, v_currMacroScope_4512_);
                v___x_4520_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__91;
                lean_inc_n(v___x_4515_, 2);
                v___x_4521_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4521_, 0, v___x_4515_);
                lean_ctor_set(v___x_4521_, 1, v___x_4517_);
                lean_ctor_set(v___x_4521_, 2, v___x_4519_);
                lean_ctor_set(v___x_4521_, 3, v___x_4520_);
                v___x_4522_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4523_ = l_Lean_Syntax_node1(v___x_4515_, v___x_4522_, v_a_4506_);
                v___x_4524_ =
                    l_Lean_Syntax_node2(v___x_4515_, v___x_4516_, v___x_4521_, v___x_4523_);
                if v_isShared_4510_ == 0 {
                    lean_ctor_set(v___x_4509_, 0, v___x_4524_);
                    v___x_4526_ = v___x_4509_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_a_4507_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4526_;
            }
            17 => {
                v_quotContext_4537_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4538_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4539_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4540_ = 0;
                v___x_4541_ = l_Lean_SourceInfo_fromRef(v_ref_4539_, v___x_4540_);
                v___x_4542_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4543_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93);
                v___x_4544_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95;
                lean_inc_n(v_currMacroScope_4538_, 3);
                lean_inc_n(v_quotContext_4537_, 3);
                v___x_4545_ =
                    l_Lean_addMacroScope(v_quotContext_4537_, v___x_4544_, v_currMacroScope_4538_);
                v___x_4546_ = lean_box(0);
                v___x_4547_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99;
                lean_inc_n(v___x_4541_, 13);
                v___x_4548_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4548_, 0, v___x_4541_);
                lean_ctor_set(v___x_4548_, 1, v___x_4543_);
                lean_ctor_set(v___x_4548_, 2, v___x_4545_);
                lean_ctor_set(v___x_4548_, 3, v___x_4547_);
                v___x_4549_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4550_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4551_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4552_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4553_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4553_, 0, v___x_4541_);
                lean_ctor_set(v___x_4553_, 1, v___x_4552_);
                v___x_4554_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4555_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4556_ = lean_box(0);
                v___x_4557_ =
                    l_Lean_addMacroScope(v_quotContext_4537_, v___x_4556_, v_currMacroScope_4538_);
                v___x_4558_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4559_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4559_, 0, v___x_4541_);
                lean_ctor_set(v___x_4559_, 1, v___x_4555_);
                lean_ctor_set(v___x_4559_, 2, v___x_4557_);
                lean_ctor_set(v___x_4559_, 3, v___x_4558_);
                v___x_4560_ = l_Lean_Syntax_node1(v___x_4541_, v___x_4554_, v___x_4559_);
                v___x_4561_ =
                    l_Lean_Syntax_node2(v___x_4541_, v___x_4551_, v___x_4553_, v___x_4560_);
                v___x_4562_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4563_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4564_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4564_, 0, v___x_4541_);
                lean_ctor_set(v___x_4564_, 1, v___x_4563_);
                v___x_4565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78);
                v___x_4566_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79;
                v___x_4567_ =
                    l_Lean_addMacroScope(v_quotContext_4537_, v___x_4566_, v_currMacroScope_4538_);
                v___x_4568_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4568_, 0, v___x_4541_);
                lean_ctor_set(v___x_4568_, 1, v___x_4565_);
                lean_ctor_set(v___x_4568_, 2, v___x_4567_);
                lean_ctor_set(v___x_4568_, 3, v___x_4546_);
                v___x_4569_ =
                    l_Lean_Syntax_node2(v___x_4541_, v___x_4562_, v___x_4564_, v___x_4568_);
                v___x_4570_ = l_Lean_Syntax_node1(v___x_4541_, v___x_4549_, v_a_4532_);
                v___x_4571_ =
                    l_Lean_Syntax_node2(v___x_4541_, v___x_4542_, v___x_4569_, v___x_4570_);
                v___x_4572_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4573_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4573_, 0, v___x_4541_);
                lean_ctor_set(v___x_4573_, 1, v___x_4572_);
                v___x_4574_ = l_Lean_Syntax_node3(
                    v___x_4541_,
                    v___x_4550_,
                    v___x_4561_,
                    v___x_4571_,
                    v___x_4573_,
                );
                v___x_4575_ = l_Lean_Syntax_node1(v___x_4541_, v___x_4549_, v___x_4574_);
                v___x_4576_ =
                    l_Lean_Syntax_node2(v___x_4541_, v___x_4542_, v___x_4548_, v___x_4575_);
                if v_isShared_4536_ == 0 {
                    lean_ctor_set(v___x_4535_, 0, v___x_4576_);
                    v___x_4578_ = v___x_4535_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
                    lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_a_4533_);
                    v___x_4578_ = v_reuseFailAlloc_4579_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4578_;
            }
            19 => {
                v_quotContext_4589_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4590_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4591_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4592_ = 0;
                v___x_4593_ = l_Lean_SourceInfo_fromRef(v_ref_4591_, v___x_4592_);
                v___x_4594_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4595_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__93);
                v___x_4596_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__95;
                lean_inc_n(v_currMacroScope_4590_, 3);
                lean_inc_n(v_quotContext_4589_, 3);
                v___x_4597_ =
                    l_Lean_addMacroScope(v_quotContext_4589_, v___x_4596_, v_currMacroScope_4590_);
                v___x_4598_ = lean_box(0);
                v___x_4599_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__99;
                lean_inc_n(v___x_4593_, 13);
                v___x_4600_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4600_, 0, v___x_4593_);
                lean_ctor_set(v___x_4600_, 1, v___x_4595_);
                lean_ctor_set(v___x_4600_, 2, v___x_4597_);
                lean_ctor_set(v___x_4600_, 3, v___x_4599_);
                v___x_4601_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4602_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4603_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4604_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4605_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4605_, 0, v___x_4593_);
                lean_ctor_set(v___x_4605_, 1, v___x_4604_);
                v___x_4606_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4607_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4608_ = lean_box(0);
                v___x_4609_ =
                    l_Lean_addMacroScope(v_quotContext_4589_, v___x_4608_, v_currMacroScope_4590_);
                v___x_4610_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4611_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4611_, 0, v___x_4593_);
                lean_ctor_set(v___x_4611_, 1, v___x_4607_);
                lean_ctor_set(v___x_4611_, 2, v___x_4609_);
                lean_ctor_set(v___x_4611_, 3, v___x_4610_);
                v___x_4612_ = l_Lean_Syntax_node1(v___x_4593_, v___x_4606_, v___x_4611_);
                v___x_4613_ =
                    l_Lean_Syntax_node2(v___x_4593_, v___x_4603_, v___x_4605_, v___x_4612_);
                v___x_4614_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4615_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4616_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4616_, 0, v___x_4593_);
                lean_ctor_set(v___x_4616_, 1, v___x_4615_);
                v___x_4617_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82);
                v___x_4618_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83;
                v___x_4619_ =
                    l_Lean_addMacroScope(v_quotContext_4589_, v___x_4618_, v_currMacroScope_4590_);
                v___x_4620_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4620_, 0, v___x_4593_);
                lean_ctor_set(v___x_4620_, 1, v___x_4617_);
                lean_ctor_set(v___x_4620_, 2, v___x_4619_);
                lean_ctor_set(v___x_4620_, 3, v___x_4598_);
                v___x_4621_ =
                    l_Lean_Syntax_node2(v___x_4593_, v___x_4614_, v___x_4616_, v___x_4620_);
                v___x_4622_ = l_Lean_Syntax_node1(v___x_4593_, v___x_4601_, v_a_4584_);
                v___x_4623_ =
                    l_Lean_Syntax_node2(v___x_4593_, v___x_4594_, v___x_4621_, v___x_4622_);
                v___x_4624_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4625_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4625_, 0, v___x_4593_);
                lean_ctor_set(v___x_4625_, 1, v___x_4624_);
                v___x_4626_ = l_Lean_Syntax_node3(
                    v___x_4593_,
                    v___x_4602_,
                    v___x_4613_,
                    v___x_4623_,
                    v___x_4625_,
                );
                v___x_4627_ = l_Lean_Syntax_node1(v___x_4593_, v___x_4601_, v___x_4626_);
                v___x_4628_ =
                    l_Lean_Syntax_node2(v___x_4593_, v___x_4594_, v___x_4600_, v___x_4627_);
                if v_isShared_4588_ == 0 {
                    lean_ctor_set(v___x_4587_, 0, v___x_4628_);
                    v___x_4630_ = v___x_4587_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
                    lean_ctor_set(v_reuseFailAlloc_4631_, 1, v_a_4585_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4630_;
            }
            21 => {
                v_quotContext_4640_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4641_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4642_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4643_ = 0;
                v___x_4644_ = l_Lean_SourceInfo_fromRef(v_ref_4642_, v___x_4643_);
                v___x_4645_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4646_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__101);
                v___x_4647_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__103;
                lean_inc(v_currMacroScope_4641_);
                lean_inc(v_quotContext_4640_);
                v___x_4648_ =
                    l_Lean_addMacroScope(v_quotContext_4640_, v___x_4647_, v_currMacroScope_4641_);
                v___x_4649_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__107;
                lean_inc_n(v___x_4644_, 2);
                v___x_4650_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4650_, 0, v___x_4644_);
                lean_ctor_set(v___x_4650_, 1, v___x_4646_);
                lean_ctor_set(v___x_4650_, 2, v___x_4648_);
                lean_ctor_set(v___x_4650_, 3, v___x_4649_);
                v___x_4651_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4652_ = l_Lean_Syntax_node1(v___x_4644_, v___x_4651_, v_a_4635_);
                v___x_4653_ =
                    l_Lean_Syntax_node2(v___x_4644_, v___x_4645_, v___x_4650_, v___x_4652_);
                if v_isShared_4639_ == 0 {
                    lean_ctor_set(v___x_4638_, 0, v___x_4653_);
                    v___x_4655_ = v___x_4638_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_a_4636_);
                    v___x_4655_ = v_reuseFailAlloc_4656_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4655_;
            }
            23 => {
                v_quotContext_4665_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4666_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4667_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4668_ = 0;
                v___x_4669_ = l_Lean_SourceInfo_fromRef(v_ref_4667_, v___x_4668_);
                v___x_4670_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4671_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__109);
                v___x_4672_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__111;
                lean_inc(v_currMacroScope_4666_);
                lean_inc(v_quotContext_4665_);
                v___x_4673_ =
                    l_Lean_addMacroScope(v_quotContext_4665_, v___x_4672_, v_currMacroScope_4666_);
                v___x_4674_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__115;
                lean_inc_n(v___x_4669_, 2);
                v___x_4675_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4675_, 0, v___x_4669_);
                lean_ctor_set(v___x_4675_, 1, v___x_4671_);
                lean_ctor_set(v___x_4675_, 2, v___x_4673_);
                lean_ctor_set(v___x_4675_, 3, v___x_4674_);
                v___x_4676_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4677_ = l_Lean_Syntax_node1(v___x_4669_, v___x_4676_, v_a_4660_);
                v___x_4678_ =
                    l_Lean_Syntax_node2(v___x_4669_, v___x_4670_, v___x_4675_, v___x_4677_);
                if v_isShared_4664_ == 0 {
                    lean_ctor_set(v___x_4663_, 0, v___x_4678_);
                    v___x_4680_ = v___x_4663_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
                    lean_ctor_set(v_reuseFailAlloc_4681_, 1, v_a_4661_);
                    v___x_4680_ = v_reuseFailAlloc_4681_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4680_;
            }
            25 => {
                v_quotContext_4690_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4691_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4692_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4693_ = 0;
                v___x_4694_ = l_Lean_SourceInfo_fromRef(v_ref_4692_, v___x_4693_);
                v___x_4695_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4696_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__117);
                v___x_4697_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__119;
                lean_inc(v_currMacroScope_4691_);
                lean_inc(v_quotContext_4690_);
                v___x_4698_ =
                    l_Lean_addMacroScope(v_quotContext_4690_, v___x_4697_, v_currMacroScope_4691_);
                v___x_4699_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__123;
                lean_inc_n(v___x_4694_, 2);
                v___x_4700_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4700_, 0, v___x_4694_);
                lean_ctor_set(v___x_4700_, 1, v___x_4696_);
                lean_ctor_set(v___x_4700_, 2, v___x_4698_);
                lean_ctor_set(v___x_4700_, 3, v___x_4699_);
                v___x_4701_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4702_ = l_Lean_Syntax_node1(v___x_4694_, v___x_4701_, v_a_4685_);
                v___x_4703_ =
                    l_Lean_Syntax_node2(v___x_4694_, v___x_4695_, v___x_4700_, v___x_4702_);
                if v_isShared_4689_ == 0 {
                    lean_ctor_set(v___x_4688_, 0, v___x_4703_);
                    v___x_4705_ = v___x_4688_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4703_);
                    lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_a_4686_);
                    v___x_4705_ = v_reuseFailAlloc_4706_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4705_;
            }
            27 => {
                v_quotContext_4716_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4717_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4718_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4719_ = 0;
                v___x_4720_ = l_Lean_SourceInfo_fromRef(v_ref_4718_, v___x_4719_);
                v___x_4721_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4722_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125);
                v___x_4723_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127;
                lean_inc_n(v_currMacroScope_4717_, 3);
                lean_inc_n(v_quotContext_4716_, 3);
                v___x_4724_ =
                    l_Lean_addMacroScope(v_quotContext_4716_, v___x_4723_, v_currMacroScope_4717_);
                v___x_4725_ = lean_box(0);
                v___x_4726_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131;
                lean_inc_n(v___x_4720_, 13);
                v___x_4727_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4727_, 0, v___x_4720_);
                lean_ctor_set(v___x_4727_, 1, v___x_4722_);
                lean_ctor_set(v___x_4727_, 2, v___x_4724_);
                lean_ctor_set(v___x_4727_, 3, v___x_4726_);
                v___x_4728_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4729_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4730_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4731_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4732_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4732_, 0, v___x_4720_);
                lean_ctor_set(v___x_4732_, 1, v___x_4731_);
                v___x_4733_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4734_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4735_ = lean_box(0);
                v___x_4736_ =
                    l_Lean_addMacroScope(v_quotContext_4716_, v___x_4735_, v_currMacroScope_4717_);
                v___x_4737_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4738_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4738_, 0, v___x_4720_);
                lean_ctor_set(v___x_4738_, 1, v___x_4734_);
                lean_ctor_set(v___x_4738_, 2, v___x_4736_);
                lean_ctor_set(v___x_4738_, 3, v___x_4737_);
                v___x_4739_ = l_Lean_Syntax_node1(v___x_4720_, v___x_4733_, v___x_4738_);
                v___x_4740_ =
                    l_Lean_Syntax_node2(v___x_4720_, v___x_4730_, v___x_4732_, v___x_4739_);
                v___x_4741_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4742_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4743_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4743_, 0, v___x_4720_);
                lean_ctor_set(v___x_4743_, 1, v___x_4742_);
                v___x_4744_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__78);
                v___x_4745_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__79;
                v___x_4746_ =
                    l_Lean_addMacroScope(v_quotContext_4716_, v___x_4745_, v_currMacroScope_4717_);
                v___x_4747_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4747_, 0, v___x_4720_);
                lean_ctor_set(v___x_4747_, 1, v___x_4744_);
                lean_ctor_set(v___x_4747_, 2, v___x_4746_);
                lean_ctor_set(v___x_4747_, 3, v___x_4725_);
                v___x_4748_ =
                    l_Lean_Syntax_node2(v___x_4720_, v___x_4741_, v___x_4743_, v___x_4747_);
                v___x_4749_ = l_Lean_Syntax_node1(v___x_4720_, v___x_4728_, v_a_4711_);
                v___x_4750_ =
                    l_Lean_Syntax_node2(v___x_4720_, v___x_4721_, v___x_4748_, v___x_4749_);
                v___x_4751_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4752_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4752_, 0, v___x_4720_);
                lean_ctor_set(v___x_4752_, 1, v___x_4751_);
                v___x_4753_ = l_Lean_Syntax_node3(
                    v___x_4720_,
                    v___x_4729_,
                    v___x_4740_,
                    v___x_4750_,
                    v___x_4752_,
                );
                v___x_4754_ = l_Lean_Syntax_node1(v___x_4720_, v___x_4728_, v___x_4753_);
                v___x_4755_ =
                    l_Lean_Syntax_node2(v___x_4720_, v___x_4721_, v___x_4727_, v___x_4754_);
                if v_isShared_4715_ == 0 {
                    lean_ctor_set(v___x_4714_, 0, v___x_4755_);
                    v___x_4757_ = v___x_4714_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_a_4712_);
                    v___x_4757_ = v_reuseFailAlloc_4758_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4757_;
            }
            29 => {
                v_quotContext_4768_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4769_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4770_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4771_ = 0;
                v___x_4772_ = l_Lean_SourceInfo_fromRef(v_ref_4770_, v___x_4771_);
                v___x_4773_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4774_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__125);
                v___x_4775_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__127;
                lean_inc_n(v_currMacroScope_4769_, 3);
                lean_inc_n(v_quotContext_4768_, 3);
                v___x_4776_ =
                    l_Lean_addMacroScope(v_quotContext_4768_, v___x_4775_, v_currMacroScope_4769_);
                v___x_4777_ = lean_box(0);
                v___x_4778_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__131;
                lean_inc_n(v___x_4772_, 13);
                v___x_4779_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4779_, 0, v___x_4772_);
                lean_ctor_set(v___x_4779_, 1, v___x_4774_);
                lean_ctor_set(v___x_4779_, 2, v___x_4776_);
                lean_ctor_set(v___x_4779_, 3, v___x_4778_);
                v___x_4780_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4781_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__50;
                v___x_4782_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__52;
                v___x_4783_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__53;
                v___x_4784_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4784_, 0, v___x_4772_);
                lean_ctor_set(v___x_4784_, 1, v___x_4783_);
                v___x_4785_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__55;
                v___x_4786_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__57);
                v___x_4787_ = lean_box(0);
                v___x_4788_ =
                    l_Lean_addMacroScope(v_quotContext_4768_, v___x_4787_, v_currMacroScope_4769_);
                v___x_4789_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__73;
                v___x_4790_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4790_, 0, v___x_4772_);
                lean_ctor_set(v___x_4790_, 1, v___x_4786_);
                lean_ctor_set(v___x_4790_, 2, v___x_4788_);
                lean_ctor_set(v___x_4790_, 3, v___x_4789_);
                v___x_4791_ = l_Lean_Syntax_node1(v___x_4772_, v___x_4785_, v___x_4790_);
                v___x_4792_ =
                    l_Lean_Syntax_node2(v___x_4772_, v___x_4782_, v___x_4784_, v___x_4791_);
                v___x_4793_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_4794_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                v___x_4795_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4795_, 0, v___x_4772_);
                lean_ctor_set(v___x_4795_, 1, v___x_4794_);
                v___x_4796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__82);
                v___x_4797_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__83;
                v___x_4798_ =
                    l_Lean_addMacroScope(v_quotContext_4768_, v___x_4797_, v_currMacroScope_4769_);
                v___x_4799_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4799_, 0, v___x_4772_);
                lean_ctor_set(v___x_4799_, 1, v___x_4796_);
                lean_ctor_set(v___x_4799_, 2, v___x_4798_);
                lean_ctor_set(v___x_4799_, 3, v___x_4777_);
                v___x_4800_ =
                    l_Lean_Syntax_node2(v___x_4772_, v___x_4793_, v___x_4795_, v___x_4799_);
                v___x_4801_ = l_Lean_Syntax_node1(v___x_4772_, v___x_4780_, v_a_4763_);
                v___x_4802_ =
                    l_Lean_Syntax_node2(v___x_4772_, v___x_4773_, v___x_4800_, v___x_4801_);
                v___x_4803_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__80;
                v___x_4804_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4804_, 0, v___x_4772_);
                lean_ctor_set(v___x_4804_, 1, v___x_4803_);
                v___x_4805_ = l_Lean_Syntax_node3(
                    v___x_4772_,
                    v___x_4781_,
                    v___x_4792_,
                    v___x_4802_,
                    v___x_4804_,
                );
                v___x_4806_ = l_Lean_Syntax_node1(v___x_4772_, v___x_4780_, v___x_4805_);
                v___x_4807_ =
                    l_Lean_Syntax_node2(v___x_4772_, v___x_4773_, v___x_4779_, v___x_4806_);
                if v_isShared_4767_ == 0 {
                    lean_ctor_set(v___x_4766_, 0, v___x_4807_);
                    v___x_4809_ = v___x_4766_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_a_4764_);
                    v___x_4809_ = v_reuseFailAlloc_4810_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4809_;
            }
            31 => {
                v_quotContext_4819_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4820_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4821_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4822_ = 0;
                v___x_4823_ = l_Lean_SourceInfo_fromRef(v_ref_4821_, v___x_4822_);
                v___x_4824_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4825_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__133);
                v___x_4826_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__135;
                lean_inc(v_currMacroScope_4820_);
                lean_inc(v_quotContext_4819_);
                v___x_4827_ =
                    l_Lean_addMacroScope(v_quotContext_4819_, v___x_4826_, v_currMacroScope_4820_);
                v___x_4828_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__139;
                lean_inc_n(v___x_4823_, 2);
                v___x_4829_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4829_, 0, v___x_4823_);
                lean_ctor_set(v___x_4829_, 1, v___x_4825_);
                lean_ctor_set(v___x_4829_, 2, v___x_4827_);
                lean_ctor_set(v___x_4829_, 3, v___x_4828_);
                v___x_4830_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4831_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4830_, v_a_4814_);
                v___x_4832_ =
                    l_Lean_Syntax_node2(v___x_4823_, v___x_4824_, v___x_4829_, v___x_4831_);
                if v_isShared_4818_ == 0 {
                    lean_ctor_set(v___x_4817_, 0, v___x_4832_);
                    v___x_4834_ = v___x_4817_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4832_);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_a_4815_);
                    v___x_4834_ = v_reuseFailAlloc_4835_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4834_;
            }
            33 => {
                v_quotContext_4844_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4845_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4846_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4847_ = 0;
                v___x_4848_ = l_Lean_SourceInfo_fromRef(v_ref_4846_, v___x_4847_);
                v___x_4849_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4850_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__141);
                v___x_4851_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__143;
                lean_inc(v_currMacroScope_4845_);
                lean_inc(v_quotContext_4844_);
                v___x_4852_ =
                    l_Lean_addMacroScope(v_quotContext_4844_, v___x_4851_, v_currMacroScope_4845_);
                v___x_4853_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__147;
                lean_inc_n(v___x_4848_, 2);
                v___x_4854_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4854_, 0, v___x_4848_);
                lean_ctor_set(v___x_4854_, 1, v___x_4850_);
                lean_ctor_set(v___x_4854_, 2, v___x_4852_);
                lean_ctor_set(v___x_4854_, 3, v___x_4853_);
                v___x_4855_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4856_ = l_Lean_Syntax_node1(v___x_4848_, v___x_4855_, v_a_4839_);
                v___x_4857_ =
                    l_Lean_Syntax_node2(v___x_4848_, v___x_4849_, v___x_4854_, v___x_4856_);
                if v_isShared_4843_ == 0 {
                    lean_ctor_set(v___x_4842_, 0, v___x_4857_);
                    v___x_4859_ = v___x_4842_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
                    lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_a_4840_);
                    v___x_4859_ = v_reuseFailAlloc_4860_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4859_;
            }
            35 => {
                v_quotContext_4869_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4870_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4871_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4872_ = 0;
                v___x_4873_ = l_Lean_SourceInfo_fromRef(v_ref_4871_, v___x_4872_);
                v___x_4874_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4875_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__149);
                v___x_4876_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__151;
                lean_inc(v_currMacroScope_4870_);
                lean_inc(v_quotContext_4869_);
                v___x_4877_ =
                    l_Lean_addMacroScope(v_quotContext_4869_, v___x_4876_, v_currMacroScope_4870_);
                v___x_4878_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__155;
                lean_inc_n(v___x_4873_, 2);
                v___x_4879_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4879_, 0, v___x_4873_);
                lean_ctor_set(v___x_4879_, 1, v___x_4875_);
                lean_ctor_set(v___x_4879_, 2, v___x_4877_);
                lean_ctor_set(v___x_4879_, 3, v___x_4878_);
                v___x_4880_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4881_ = l_Lean_Syntax_node1(v___x_4873_, v___x_4880_, v_a_4864_);
                v___x_4882_ =
                    l_Lean_Syntax_node2(v___x_4873_, v___x_4874_, v___x_4879_, v___x_4881_);
                if v_isShared_4868_ == 0 {
                    lean_ctor_set(v___x_4867_, 0, v___x_4882_);
                    v___x_4884_ = v___x_4867_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
                    lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_a_4865_);
                    v___x_4884_ = v_reuseFailAlloc_4885_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4884_;
            }
            37 => {
                v_quotContext_4894_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4895_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4896_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4897_ = 0;
                v___x_4898_ = l_Lean_SourceInfo_fromRef(v_ref_4896_, v___x_4897_);
                v___x_4899_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4900_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__157);
                v___x_4901_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__159;
                lean_inc(v_currMacroScope_4895_);
                lean_inc(v_quotContext_4894_);
                v___x_4902_ =
                    l_Lean_addMacroScope(v_quotContext_4894_, v___x_4901_, v_currMacroScope_4895_);
                v___x_4903_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__163;
                lean_inc_n(v___x_4898_, 2);
                v___x_4904_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4904_, 0, v___x_4898_);
                lean_ctor_set(v___x_4904_, 1, v___x_4900_);
                lean_ctor_set(v___x_4904_, 2, v___x_4902_);
                lean_ctor_set(v___x_4904_, 3, v___x_4903_);
                v___x_4905_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4906_ = l_Lean_Syntax_node1(v___x_4898_, v___x_4905_, v_a_4889_);
                v___x_4907_ =
                    l_Lean_Syntax_node2(v___x_4898_, v___x_4899_, v___x_4904_, v___x_4906_);
                if v_isShared_4893_ == 0 {
                    lean_ctor_set(v___x_4892_, 0, v___x_4907_);
                    v___x_4909_ = v___x_4892_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4907_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_a_4890_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4909_;
            }
            39 => {
                v_quotContext_4919_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4920_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4921_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4922_ = 0;
                v___x_4923_ = l_Lean_SourceInfo_fromRef(v_ref_4921_, v___x_4922_);
                v___x_4924_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4925_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__165);
                v___x_4926_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__167;
                lean_inc(v_currMacroScope_4920_);
                lean_inc(v_quotContext_4919_);
                v___x_4927_ =
                    l_Lean_addMacroScope(v_quotContext_4919_, v___x_4926_, v_currMacroScope_4920_);
                v___x_4928_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__171;
                lean_inc_n(v___x_4923_, 2);
                v___x_4929_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4929_, 0, v___x_4923_);
                lean_ctor_set(v___x_4929_, 1, v___x_4925_);
                lean_ctor_set(v___x_4929_, 2, v___x_4927_);
                lean_ctor_set(v___x_4929_, 3, v___x_4928_);
                v___x_4930_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4931_ = l_Lean_Syntax_node1(v___x_4923_, v___x_4930_, v_a_4914_);
                v___x_4932_ =
                    l_Lean_Syntax_node2(v___x_4923_, v___x_4924_, v___x_4929_, v___x_4931_);
                if v_isShared_4918_ == 0 {
                    lean_ctor_set(v___x_4917_, 0, v___x_4932_);
                    v___x_4934_ = v___x_4917_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
                    lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_a_4915_);
                    v___x_4934_ = v_reuseFailAlloc_4935_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4934_;
            }
            41 => {
                v_quotContext_4944_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4945_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4946_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4947_ = 0;
                v___x_4948_ = l_Lean_SourceInfo_fromRef(v_ref_4946_, v___x_4947_);
                v___x_4949_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__173);
                v___x_4951_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__175;
                lean_inc(v_currMacroScope_4945_);
                lean_inc(v_quotContext_4944_);
                v___x_4952_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_4951_, v_currMacroScope_4945_);
                v___x_4953_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__179;
                lean_inc_n(v___x_4948_, 2);
                v___x_4954_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4954_, 0, v___x_4948_);
                lean_ctor_set(v___x_4954_, 1, v___x_4950_);
                lean_ctor_set(v___x_4954_, 2, v___x_4952_);
                lean_ctor_set(v___x_4954_, 3, v___x_4953_);
                v___x_4955_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4956_ = l_Lean_Syntax_node1(v___x_4948_, v___x_4955_, v_a_4939_);
                v___x_4957_ =
                    l_Lean_Syntax_node2(v___x_4948_, v___x_4949_, v___x_4954_, v___x_4956_);
                if v_isShared_4943_ == 0 {
                    lean_ctor_set(v___x_4942_, 0, v___x_4957_);
                    v___x_4959_ = v___x_4942_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_a_4940_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4959_;
            }
            43 => {
                v_quotContext_4969_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4970_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4971_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4972_ = 0;
                v___x_4973_ = l_Lean_SourceInfo_fromRef(v_ref_4971_, v___x_4972_);
                v___x_4974_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_4975_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__181);
                v___x_4976_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__183;
                lean_inc(v_currMacroScope_4970_);
                lean_inc(v_quotContext_4969_);
                v___x_4977_ =
                    l_Lean_addMacroScope(v_quotContext_4969_, v___x_4976_, v_currMacroScope_4970_);
                v___x_4978_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__187;
                lean_inc_n(v___x_4973_, 2);
                v___x_4979_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4979_, 0, v___x_4973_);
                lean_ctor_set(v___x_4979_, 1, v___x_4975_);
                lean_ctor_set(v___x_4979_, 2, v___x_4977_);
                lean_ctor_set(v___x_4979_, 3, v___x_4978_);
                v___x_4980_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_4981_ = l_Lean_Syntax_node1(v___x_4973_, v___x_4980_, v_a_4964_);
                v___x_4982_ =
                    l_Lean_Syntax_node2(v___x_4973_, v___x_4974_, v___x_4979_, v___x_4981_);
                if v_isShared_4968_ == 0 {
                    lean_ctor_set(v___x_4967_, 0, v___x_4982_);
                    v___x_4984_ = v___x_4967_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
                    lean_ctor_set(v_reuseFailAlloc_4985_, 1, v_a_4965_);
                    v___x_4984_ = v_reuseFailAlloc_4985_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4984_;
            }
            45 => {
                v_quotContext_4994_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_4995_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_4996_ = lean_ctor_get(v_a_4273_, 5);
                v___x_4997_ = 0;
                v___x_4998_ = l_Lean_SourceInfo_fromRef(v_ref_4996_, v___x_4997_);
                v___x_4999_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5000_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__189);
                v___x_5001_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__191;
                lean_inc(v_currMacroScope_4995_);
                lean_inc(v_quotContext_4994_);
                v___x_5002_ =
                    l_Lean_addMacroScope(v_quotContext_4994_, v___x_5001_, v_currMacroScope_4995_);
                v___x_5003_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__195;
                lean_inc_n(v___x_4998_, 2);
                v___x_5004_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5004_, 0, v___x_4998_);
                lean_ctor_set(v___x_5004_, 1, v___x_5000_);
                lean_ctor_set(v___x_5004_, 2, v___x_5002_);
                lean_ctor_set(v___x_5004_, 3, v___x_5003_);
                v___x_5005_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5006_ = l_Lean_Syntax_node1(v___x_4998_, v___x_5005_, v_a_4989_);
                v___x_5007_ =
                    l_Lean_Syntax_node2(v___x_4998_, v___x_4999_, v___x_5004_, v___x_5006_);
                if v_isShared_4993_ == 0 {
                    lean_ctor_set(v___x_4992_, 0, v___x_5007_);
                    v___x_5009_ = v___x_4992_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5007_);
                    lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_a_4990_);
                    v___x_5009_ = v_reuseFailAlloc_5010_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5009_;
            }
            47 => {
                v_quotContext_5019_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5020_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5021_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5022_ = 0;
                v___x_5023_ = l_Lean_SourceInfo_fromRef(v_ref_5021_, v___x_5022_);
                v___x_5024_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5025_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__197);
                v___x_5026_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__199;
                lean_inc(v_currMacroScope_5020_);
                lean_inc(v_quotContext_5019_);
                v___x_5027_ =
                    l_Lean_addMacroScope(v_quotContext_5019_, v___x_5026_, v_currMacroScope_5020_);
                v___x_5028_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__203;
                lean_inc_n(v___x_5023_, 2);
                v___x_5029_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5029_, 0, v___x_5023_);
                lean_ctor_set(v___x_5029_, 1, v___x_5025_);
                lean_ctor_set(v___x_5029_, 2, v___x_5027_);
                lean_ctor_set(v___x_5029_, 3, v___x_5028_);
                v___x_5030_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5031_ = l_Lean_Syntax_node1(v___x_5023_, v___x_5030_, v_a_5014_);
                v___x_5032_ =
                    l_Lean_Syntax_node2(v___x_5023_, v___x_5024_, v___x_5029_, v___x_5031_);
                if v_isShared_5018_ == 0 {
                    lean_ctor_set(v___x_5017_, 0, v___x_5032_);
                    v___x_5034_ = v___x_5017_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 1, v_a_5015_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5034_;
            }
            49 => {
                v_quotContext_5044_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5045_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5046_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5047_ = 0;
                v___x_5048_ = l_Lean_SourceInfo_fromRef(v_ref_5046_, v___x_5047_);
                v___x_5049_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5050_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__205);
                v___x_5051_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__207;
                lean_inc(v_currMacroScope_5045_);
                lean_inc(v_quotContext_5044_);
                v___x_5052_ =
                    l_Lean_addMacroScope(v_quotContext_5044_, v___x_5051_, v_currMacroScope_5045_);
                v___x_5053_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__211;
                lean_inc_n(v___x_5048_, 2);
                v___x_5054_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5054_, 0, v___x_5048_);
                lean_ctor_set(v___x_5054_, 1, v___x_5050_);
                lean_ctor_set(v___x_5054_, 2, v___x_5052_);
                lean_ctor_set(v___x_5054_, 3, v___x_5053_);
                v___x_5055_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5056_ = l_Lean_Syntax_node1(v___x_5048_, v___x_5055_, v_a_5039_);
                v___x_5057_ =
                    l_Lean_Syntax_node2(v___x_5048_, v___x_5049_, v___x_5054_, v___x_5056_);
                if v_isShared_5043_ == 0 {
                    lean_ctor_set(v___x_5042_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5042_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_a_5040_);
                    v___x_5059_ = v_reuseFailAlloc_5060_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5059_;
            }
            51 => {
                v_quotContext_5069_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5070_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5071_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5072_ = 0;
                v___x_5073_ = l_Lean_SourceInfo_fromRef(v_ref_5071_, v___x_5072_);
                v___x_5074_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5075_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__213);
                v___x_5076_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__215;
                lean_inc(v_currMacroScope_5070_);
                lean_inc(v_quotContext_5069_);
                v___x_5077_ =
                    l_Lean_addMacroScope(v_quotContext_5069_, v___x_5076_, v_currMacroScope_5070_);
                v___x_5078_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__219;
                lean_inc_n(v___x_5073_, 2);
                v___x_5079_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5079_, 0, v___x_5073_);
                lean_ctor_set(v___x_5079_, 1, v___x_5075_);
                lean_ctor_set(v___x_5079_, 2, v___x_5077_);
                lean_ctor_set(v___x_5079_, 3, v___x_5078_);
                v___x_5080_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5081_ = l_Lean_Syntax_node1(v___x_5073_, v___x_5080_, v_a_5064_);
                v___x_5082_ =
                    l_Lean_Syntax_node2(v___x_5073_, v___x_5074_, v___x_5079_, v___x_5081_);
                if v_isShared_5068_ == 0 {
                    lean_ctor_set(v___x_5067_, 0, v___x_5082_);
                    v___x_5084_ = v___x_5067_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5082_);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_a_5065_);
                    v___x_5084_ = v_reuseFailAlloc_5085_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5084_;
            }
            53 => {
                v_quotContext_5094_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5095_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5096_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5097_ = 0;
                v___x_5098_ = l_Lean_SourceInfo_fromRef(v_ref_5096_, v___x_5097_);
                v___x_5099_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5100_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__221);
                v___x_5101_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__223;
                lean_inc(v_currMacroScope_5095_);
                lean_inc(v_quotContext_5094_);
                v___x_5102_ =
                    l_Lean_addMacroScope(v_quotContext_5094_, v___x_5101_, v_currMacroScope_5095_);
                v___x_5103_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__227;
                lean_inc_n(v___x_5098_, 2);
                v___x_5104_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5104_, 0, v___x_5098_);
                lean_ctor_set(v___x_5104_, 1, v___x_5100_);
                lean_ctor_set(v___x_5104_, 2, v___x_5102_);
                lean_ctor_set(v___x_5104_, 3, v___x_5103_);
                v___x_5105_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5106_ = l_Lean_Syntax_node1(v___x_5098_, v___x_5105_, v_a_5089_);
                v___x_5107_ =
                    l_Lean_Syntax_node2(v___x_5098_, v___x_5099_, v___x_5104_, v___x_5106_);
                if v_isShared_5093_ == 0 {
                    lean_ctor_set(v___x_5092_, 0, v___x_5107_);
                    v___x_5109_ = v___x_5092_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5107_);
                    lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_a_5090_);
                    v___x_5109_ = v_reuseFailAlloc_5110_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5109_;
            }
            55 => {
                v_quotContext_5130_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5131_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5132_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5133_ = 0;
                v___x_5134_ = l_Lean_SourceInfo_fromRef(v_ref_5132_, v___x_5133_);
                v___x_5135_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5136_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__237);
                v___x_5137_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__239;
                lean_inc(v_currMacroScope_5131_);
                lean_inc(v_quotContext_5130_);
                v___x_5138_ =
                    l_Lean_addMacroScope(v_quotContext_5130_, v___x_5137_, v_currMacroScope_5131_);
                v___x_5139_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__243;
                lean_inc_n(v___x_5134_, 2);
                v___x_5140_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5140_, 0, v___x_5134_);
                lean_ctor_set(v___x_5140_, 1, v___x_5136_);
                lean_ctor_set(v___x_5140_, 2, v___x_5138_);
                lean_ctor_set(v___x_5140_, 3, v___x_5139_);
                v___x_5141_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5142_ = l_Lean_Syntax_node1(v___x_5134_, v___x_5141_, v_a_5125_);
                v___x_5143_ =
                    l_Lean_Syntax_node2(v___x_5134_, v___x_5135_, v___x_5140_, v___x_5142_);
                if v_isShared_5129_ == 0 {
                    lean_ctor_set(v___x_5128_, 0, v___x_5143_);
                    v___x_5145_ = v___x_5128_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5143_);
                    lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_a_5126_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5145_;
            }
            57 => {
                v_quotContext_5155_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5156_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5157_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5158_ = 0;
                v___x_5159_ = l_Lean_SourceInfo_fromRef(v_ref_5157_, v___x_5158_);
                v___x_5160_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5161_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__245);
                v___x_5162_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__247;
                lean_inc(v_currMacroScope_5156_);
                lean_inc(v_quotContext_5155_);
                v___x_5163_ =
                    l_Lean_addMacroScope(v_quotContext_5155_, v___x_5162_, v_currMacroScope_5156_);
                v___x_5164_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__251;
                lean_inc_n(v___x_5159_, 2);
                v___x_5165_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5165_, 0, v___x_5159_);
                lean_ctor_set(v___x_5165_, 1, v___x_5161_);
                lean_ctor_set(v___x_5165_, 2, v___x_5163_);
                lean_ctor_set(v___x_5165_, 3, v___x_5164_);
                v___x_5166_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5167_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5166_, v_a_5150_);
                v___x_5168_ =
                    l_Lean_Syntax_node2(v___x_5159_, v___x_5160_, v___x_5165_, v___x_5167_);
                if v_isShared_5154_ == 0 {
                    lean_ctor_set(v___x_5153_, 0, v___x_5168_);
                    v___x_5170_ = v___x_5153_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 1, v_a_5151_);
                    v___x_5170_ = v_reuseFailAlloc_5171_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_5170_;
            }
            59 => {
                v_quotContext_5180_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5181_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5182_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5183_ = 0;
                v___x_5184_ = l_Lean_SourceInfo_fromRef(v_ref_5182_, v___x_5183_);
                v___x_5185_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5186_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__253);
                v___x_5187_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__255;
                lean_inc(v_currMacroScope_5181_);
                lean_inc(v_quotContext_5180_);
                v___x_5188_ =
                    l_Lean_addMacroScope(v_quotContext_5180_, v___x_5187_, v_currMacroScope_5181_);
                v___x_5189_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__259;
                lean_inc_n(v___x_5184_, 2);
                v___x_5190_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5190_, 0, v___x_5184_);
                lean_ctor_set(v___x_5190_, 1, v___x_5186_);
                lean_ctor_set(v___x_5190_, 2, v___x_5188_);
                lean_ctor_set(v___x_5190_, 3, v___x_5189_);
                v___x_5191_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5192_ = l_Lean_Syntax_node1(v___x_5184_, v___x_5191_, v_a_5175_);
                v___x_5193_ =
                    l_Lean_Syntax_node2(v___x_5184_, v___x_5185_, v___x_5190_, v___x_5192_);
                if v_isShared_5179_ == 0 {
                    lean_ctor_set(v___x_5178_, 0, v___x_5193_);
                    v___x_5195_ = v___x_5178_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_5196_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5196_, 0, v___x_5193_);
                    lean_ctor_set(v_reuseFailAlloc_5196_, 1, v_a_5176_);
                    v___x_5195_ = v_reuseFailAlloc_5196_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_5195_;
            }
            61 => {
                v_quotContext_5205_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5206_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5207_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5208_ = 0;
                v___x_5209_ = l_Lean_SourceInfo_fromRef(v_ref_5207_, v___x_5208_);
                v___x_5210_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5211_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__261);
                v___x_5212_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__263;
                lean_inc(v_currMacroScope_5206_);
                lean_inc(v_quotContext_5205_);
                v___x_5213_ =
                    l_Lean_addMacroScope(v_quotContext_5205_, v___x_5212_, v_currMacroScope_5206_);
                v___x_5214_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__267;
                lean_inc_n(v___x_5209_, 2);
                v___x_5215_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5215_, 0, v___x_5209_);
                lean_ctor_set(v___x_5215_, 1, v___x_5211_);
                lean_ctor_set(v___x_5215_, 2, v___x_5213_);
                lean_ctor_set(v___x_5215_, 3, v___x_5214_);
                v___x_5216_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5217_ = l_Lean_Syntax_node1(v___x_5209_, v___x_5216_, v_a_5200_);
                v___x_5218_ =
                    l_Lean_Syntax_node2(v___x_5209_, v___x_5210_, v___x_5215_, v___x_5217_);
                if v_isShared_5204_ == 0 {
                    lean_ctor_set(v___x_5203_, 0, v___x_5218_);
                    v___x_5220_ = v___x_5203_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5218_);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 1, v_a_5201_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5220_;
            }
            63 => {
                v_quotContext_5230_ = lean_ctor_get(v_a_4273_, 1);
                v_currMacroScope_5231_ = lean_ctor_get(v_a_4273_, 2);
                v_ref_5232_ = lean_ctor_get(v_a_4273_, 5);
                v___x_5233_ = 0;
                v___x_5234_ = l_Lean_SourceInfo_fromRef(v_ref_5232_, v___x_5233_);
                v___x_5235_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5236_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__269);
                v___x_5237_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__271;
                lean_inc(v_currMacroScope_5231_);
                lean_inc(v_quotContext_5230_);
                v___x_5238_ =
                    l_Lean_addMacroScope(v_quotContext_5230_, v___x_5237_, v_currMacroScope_5231_);
                v___x_5239_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__275;
                lean_inc_n(v___x_5234_, 2);
                v___x_5240_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5240_, 0, v___x_5234_);
                lean_ctor_set(v___x_5240_, 1, v___x_5236_);
                lean_ctor_set(v___x_5240_, 2, v___x_5238_);
                lean_ctor_set(v___x_5240_, 3, v___x_5239_);
                v___x_5241_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5242_ = l_Lean_Syntax_node1(v___x_5234_, v___x_5241_, v_a_5225_);
                v___x_5243_ =
                    l_Lean_Syntax_node2(v___x_5234_, v___x_5235_, v___x_5240_, v___x_5242_);
                if v_isShared_5229_ == 0 {
                    lean_ctor_set(v___x_5228_, 0, v___x_5243_);
                    v___x_5245_ = v___x_5228_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5243_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_a_5226_);
                    v___x_5245_ = v_reuseFailAlloc_5246_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___boxed(
    mut v_x_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5251_: *mut LeanObject = core::ptr::null_mut();
    v_res_5251_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(
        v_x_5248_, v_a_5249_, v_a_5250_,
    );
    lean_dec_ref(v_a_5249_);
    return v_res_5251_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1()
-> *mut LeanObject {
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    v___x_5253_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__0;
    v___x_5254_ = l_String_toRawSubstring_x27(v___x_5253_);
    return v___x_5254_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4()
-> *mut LeanObject {
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    v___x_5258_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__3;
    v___x_5259_ = l_String_toRawSubstring_x27(v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(
    mut v_x_5262_: *mut LeanObject,
    mut v_a_5263_: *mut LeanObject,
    mut v_a_5264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifier_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v_quotContext_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: u8 = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5262_) == 0 {
                    v_val_5265_ = lean_ctor_get(v_x_5262_, 0);
                    lean_inc_ref(v_val_5265_);
                    lean_dec_ref_known(v_x_5262_, 1);
                    v_quotContext_5266_ = lean_ctor_get(v_a_5263_, 1);
                    v_currMacroScope_5267_ = lean_ctor_get(v_a_5263_, 2);
                    v_ref_5268_ = lean_ctor_get(v_a_5263_, 5);
                    v___x_5269_ = 0;
                    v___x_5270_ = l_Lean_SourceInfo_fromRef(v_ref_5268_, v___x_5269_);
                    v___x_5271_ =
                        l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                    v___x_5272_ =
                        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                    v___x_5273_ =
                        l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                    lean_inc_n(v___x_5270_, 4);
                    v___x_5274_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5274_, 0, v___x_5270_);
                    lean_ctor_set(v___x_5274_, 1, v___x_5273_);
                    v___x_5275_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__1);
                    v___x_5276_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__2;
                    lean_inc(v_currMacroScope_5267_);
                    lean_inc(v_quotContext_5266_);
                    v___x_5277_ = l_Lean_addMacroScope(
                        v_quotContext_5266_,
                        v___x_5276_,
                        v_currMacroScope_5267_,
                    );
                    v___x_5278_ = lean_box(0);
                    v___x_5279_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_5279_, 0, v___x_5270_);
                    lean_ctor_set(v___x_5279_, 1, v___x_5275_);
                    lean_ctor_set(v___x_5279_, 2, v___x_5277_);
                    lean_ctor_set(v___x_5279_, 3, v___x_5278_);
                    v___x_5280_ =
                        l_Lean_Syntax_node2(v___x_5270_, v___x_5272_, v___x_5274_, v___x_5279_);
                    v___x_5281_ =
                        l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                    v___x_5282_ = lean_box(2);
                    v___x_5283_ = l_Lean_Syntax_mkStrLit(v_val_5265_, v___x_5282_);
                    v___x_5284_ = l_Lean_Syntax_node1(v___x_5270_, v___x_5281_, v___x_5283_);
                    v___x_5285_ =
                        l_Lean_Syntax_node2(v___x_5270_, v___x_5271_, v___x_5280_, v___x_5284_);
                    v___x_5286_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5286_, 0, v___x_5285_);
                    lean_ctor_set(v___x_5286_, 1, v_a_5264_);
                    return v___x_5286_;
                } else {
                    v_modifier_5287_ = lean_ctor_get(v_x_5262_, 0);
                    lean_inc(v_modifier_5287_);
                    lean_dec_ref_known(v_x_5262_, 1);
                    v___x_5288_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier(
                        v_modifier_5287_,
                        v_a_5263_,
                        v_a_5264_,
                    );
                    v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
                    v_a_5290_ = lean_ctor_get(v___x_5288_, 1);
                    v_isSharedCheck_5315_ = (!lean_is_exclusive(v___x_5288_)) as u8;
                    if v_isSharedCheck_5315_ == 0 {
                        v___x_5292_ = v___x_5288_;
                        v_isShared_5293_ = v_isSharedCheck_5315_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5290_);
                        lean_inc(v_a_5289_);
                        lean_dec(v___x_5288_);
                        v___x_5292_ = lean_box(0);
                        v_isShared_5293_ = v_isSharedCheck_5315_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_5294_ = lean_ctor_get(v_a_5263_, 1);
                v_currMacroScope_5295_ = lean_ctor_get(v_a_5263_, 2);
                v_ref_5296_ = lean_ctor_get(v_a_5263_, 5);
                v___x_5297_ = 0;
                v___x_5298_ = l_Lean_SourceInfo_fromRef(v_ref_5296_, v___x_5297_);
                v___x_5299_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__4;
                v___x_5300_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__75;
                v___x_5301_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertModifier___closed__76;
                lean_inc_n(v___x_5298_, 4);
                v___x_5302_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5302_, 0, v___x_5298_);
                lean_ctor_set(v___x_5302_, 1, v___x_5301_);
                v___x_5303_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__4);
                v___x_5304_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___closed__5;
                lean_inc(v_currMacroScope_5295_);
                lean_inc(v_quotContext_5294_);
                v___x_5305_ =
                    l_Lean_addMacroScope(v_quotContext_5294_, v___x_5304_, v_currMacroScope_5295_);
                v___x_5306_ = lean_box(0);
                v___x_5307_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_5307_, 0, v___x_5298_);
                lean_ctor_set(v___x_5307_, 1, v___x_5303_);
                lean_ctor_set(v___x_5307_, 2, v___x_5305_);
                lean_ctor_set(v___x_5307_, 3, v___x_5306_);
                v___x_5308_ =
                    l_Lean_Syntax_node2(v___x_5298_, v___x_5300_, v___x_5302_, v___x_5307_);
                v___x_5309_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5310_ = l_Lean_Syntax_node1(v___x_5298_, v___x_5309_, v_a_5289_);
                v___x_5311_ =
                    l_Lean_Syntax_node2(v___x_5298_, v___x_5299_, v___x_5308_, v___x_5310_);
                if v_isShared_5293_ == 0 {
                    lean_ctor_set(v___x_5292_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
                    lean_ctor_set(v_reuseFailAlloc_5314_, 1, v_a_5290_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart___boxed(
    mut v_x_5316_: *mut LeanObject,
    mut v_a_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5319_: *mut LeanObject = core::ptr::null_mut();
    v_res_5319_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(
        v_x_5316_, v_a_5317_, v_a_5318_,
    );
    lean_dec_ref(v_a_5317_);
    return v_res_5319_;
}
pub unsafe fn l_List_foldl___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__1(
    mut v_x_5382_: *mut LeanObject,
    mut v_x_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5383_) == 0 {
                    return v_x_5382_;
                } else {
                    v_head_5384_ = lean_ctor_get(v_x_5383_, 0);
                    lean_inc(v_head_5384_);
                    v_tail_5385_ = lean_ctor_get(v_x_5383_, 1);
                    lean_inc(v_tail_5385_);
                    lean_dec_ref_known(v_x_5383_, 2);
                    v___x_5386_ = l_Std_Time_termDatespec_x28___x2c___x29___closed__2;
                    v___x_5387_ =
                        l_Lean_Syntax_TSepArray_push___redArg(v___x_5386_, v_x_5382_, v_head_5384_);
                    v_x_5382_ = v___x_5387_;
                    v_x_5383_ = v_tail_5385_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(
    mut v_x_5389_: *mut LeanObject,
    mut v_x_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5389_) == 0 {
                    v___x_5393_ = l_List_reverse___redArg(v_x_5390_);
                    v___x_5394_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5394_, 0, v___x_5393_);
                    lean_ctor_set(v___x_5394_, 1, v___y_5392_);
                    return v___x_5394_;
                } else {
                    v_head_5395_ = lean_ctor_get(v_x_5389_, 0);
                    v_tail_5396_ = lean_ctor_get(v_x_5389_, 1);
                    v_isSharedCheck_5407_ = (!lean_is_exclusive(v_x_5389_)) as u8;
                    if v_isSharedCheck_5407_ == 0 {
                        v___x_5398_ = v_x_5389_;
                        v_isShared_5399_ = v_isSharedCheck_5407_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5396_);
                        lean_inc(v_head_5395_);
                        lean_dec(v_x_5389_);
                        v___x_5398_ = lean_box(0);
                        v_isShared_5399_ = v_isSharedCheck_5407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5400_ = l___private_Std_Time_Notation_Spec_0__Std_Time_convertFormatPart(
                    v_head_5395_,
                    v___y_5391_,
                    v___y_5392_,
                );
                v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
                lean_inc(v_a_5401_);
                v_a_5402_ = lean_ctor_get(v___x_5400_, 1);
                lean_inc(v_a_5402_);
                lean_dec_ref(v___x_5400_);
                if v_isShared_5399_ == 0 {
                    lean_ctor_set(v___x_5398_, 1, v_x_5390_);
                    lean_ctor_set(v___x_5398_, 0, v_a_5401_);
                    v___x_5404_ = v___x_5398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5401_);
                    lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_x_5390_);
                    v___x_5404_ = v_reuseFailAlloc_5406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_5389_ = v_tail_5396_;
                v_x_5390_ = v___x_5404_;
                v___y_5392_ = v_a_5402_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0___boxed(
    mut v_x_5408_: *mut LeanObject,
    mut v_x_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_res_5412_ = l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(v_x_5408_, v_x_5409_, v___y_5410_, v___y_5411_);
    lean_dec_ref(v___y_5410_);
    return v_res_5412_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0()
-> *mut LeanObject {
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: u8 = 0;
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v___x_5413_ = l_Std_Time_DateFormat_enUS;
    v___x_5414_ = 0;
    v___x_5415_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5415_, 0, v___x_5413_);
    lean_ctor_set_uint8(
        v___x_5415_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5414_,
    );
    return v___x_5415_;
}
pub unsafe fn _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9()
-> *mut LeanObject {
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    v___x_5430_ = l_Array_mkArray0(lean_box(0));
    return v___x_5430_;
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(
    mut v_fmt_5459_: *mut LeanObject,
    mut v_config_5460_: *mut LeanObject,
    mut v_a_5461_: *mut LeanObject,
    mut v_a_5462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_input_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: u8 = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_format_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_string_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5482_: u8 = 0;
    let mut v_ref_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5532_: u8 = 0;
    let mut v_a_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5537_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_unused_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_input_5463_ = l_Lean_TSyntax_getString(v_fmt_5459_);
                v___x_5464_ = 0;
                v___x_5465_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__0);
                v_format_5466_ = l_Std_Time_GenericFormat_spec___redArg(v_input_5463_, v___x_5465_);
                if lean_obj_tag(v_format_5466_) == 0 {
                    lean_dec(v_config_5460_);
                    v_a_5467_ = lean_ctor_get(v_format_5466_, 0);
                    lean_inc(v_a_5467_);
                    lean_dec_ref_known(v_format_5466_, 1);
                    v___x_5468_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__1;
                    v___x_5469_ = lean_string_append(v___x_5468_, v_a_5467_);
                    lean_dec(v_a_5467_);
                    v___x_5470_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_fmt_5459_,
                        v___x_5469_,
                        v_a_5461_,
                        v_a_5462_,
                    );
                    return v___x_5470_;
                } else {
                    v_a_5471_ = lean_ctor_get(v_format_5466_, 0);
                    lean_inc(v_a_5471_);
                    lean_dec_ref_known(v_format_5466_, 1);
                    v_string_5472_ = lean_ctor_get(v_a_5471_, 1);
                    v_isSharedCheck_5542_ = (!lean_is_exclusive(v_a_5471_)) as u8;
                    if v_isSharedCheck_5542_ == 0 {
                        v_unused_5543_ = lean_ctor_get(v_a_5471_, 0);
                        lean_dec(v_unused_5543_);
                        v___x_5474_ = v_a_5471_;
                        v_isShared_5475_ = v_isSharedCheck_5542_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_string_5472_);
                        lean_dec(v_a_5471_);
                        v___x_5474_ = lean_box(0);
                        v_isShared_5475_ = v_isSharedCheck_5542_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5476_ = lean_box(0);
                v___x_5477_ = l_List_mapM_loop___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__0(v_string_5472_, v___x_5476_, v_a_5461_, v_a_5462_);
                if lean_obj_tag(v___x_5477_) == 0 {
                    v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
                    v_a_5479_ = lean_ctor_get(v___x_5477_, 1);
                    v_isSharedCheck_5532_ = (!lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5532_ == 0 {
                        v___x_5481_ = v___x_5477_;
                        v_isShared_5482_ = v_isSharedCheck_5532_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5479_);
                        lean_inc(v_a_5478_);
                        lean_dec(v___x_5477_);
                        v___x_5481_ = lean_box(0);
                        v_isShared_5482_ = v_isSharedCheck_5532_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5474_);
                    lean_dec(v_config_5460_);
                    v_a_5533_ = lean_ctor_get(v___x_5477_, 0);
                    v_a_5534_ = lean_ctor_get(v___x_5477_, 1);
                    v_isSharedCheck_5541_ = (!lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5541_ == 0 {
                        v___x_5536_ = v___x_5477_;
                        v_isShared_5537_ = v_isSharedCheck_5541_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5534_);
                        lean_inc(v_a_5533_);
                        lean_dec(v___x_5477_);
                        v___x_5536_ = lean_box(0);
                        v_isShared_5537_ = v_isSharedCheck_5541_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_ref_5483_ = lean_ctor_get(v_a_5461_, 5);
                v___x_5484_ = l_Std_Time_termDatespec_x28___x2c___x29___closed__2;
                v___x_5485_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__2;
                v___x_5486_ = l_List_foldl___at___00__private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat_spec__1(v___x_5485_, v_a_5478_);
                v___x_5513_ = l_Lean_SourceInfo_fromRef(v_ref_5483_, v___x_5464_);
                v___x_5514_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__13;
                v___x_5515_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__14;
                lean_inc_n(v___x_5513_, 7);
                v___x_5516_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5516_, 0, v___x_5513_);
                lean_ctor_set(v___x_5516_, 1, v___x_5515_);
                v___x_5517_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__15;
                v___x_5518_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5518_, 0, v___x_5513_);
                lean_ctor_set(v___x_5518_, 1, v___x_5517_);
                lean_inc_ref(v___x_5518_);
                lean_inc_ref(v___x_5516_);
                v___x_5519_ =
                    l_Lean_Syntax_node2(v___x_5513_, v___x_5514_, v___x_5516_, v___x_5518_);
                v___x_5520_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__17;
                v___x_5521_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                v___x_5522_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9);
                v___x_5523_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5523_, 0, v___x_5513_);
                lean_ctor_set(v___x_5523_, 1, v___x_5521_);
                lean_ctor_set(v___x_5523_, 2, v___x_5522_);
                v___x_5524_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__19;
                lean_inc_ref_n(v___x_5523_, 3);
                v___x_5525_ = l_Lean_Syntax_node1(v___x_5513_, v___x_5524_, v___x_5523_);
                v___x_5526_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__21;
                v___x_5527_ = l_Lean_Syntax_node1(v___x_5513_, v___x_5526_, v___x_5523_);
                v___x_5528_ = l_Lean_Syntax_node6(
                    v___x_5513_,
                    v___x_5520_,
                    v___x_5516_,
                    v___x_5523_,
                    v___x_5525_,
                    v___x_5527_,
                    v___x_5523_,
                    v___x_5518_,
                );
                if lean_obj_tag(v_config_5460_) == 0 {
                    v___x_5529_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__23;
                    v___x_5530_ =
                        l_Lean_Syntax_node2(v___x_5513_, v___x_5529_, v___x_5519_, v___x_5528_);
                    v___y_5488_ = v___x_5530_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_5528_);
                    lean_dec(v___x_5519_);
                    lean_dec(v___x_5513_);
                    v_val_5531_ = lean_ctor_get(v_config_5460_, 0);
                    lean_inc(v_val_5531_);
                    lean_dec_ref_known(v_config_5460_, 1);
                    v___y_5488_ = v_val_5531_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5489_ = l_Lean_SourceInfo_fromRef(v_ref_5483_, v___x_5464_);
                v___x_5490_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__4;
                v___x_5491_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__5;
                lean_inc(v___x_5489_);
                if v_isShared_5475_ == 0 {
                    lean_ctor_set_tag(v___x_5474_, 2);
                    lean_ctor_set(v___x_5474_, 1, v___x_5491_);
                    lean_ctor_set(v___x_5474_, 0, v___x_5489_);
                    v___x_5493_ = v___x_5474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5512_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5489_);
                    lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5491_);
                    v___x_5493_ = v_reuseFailAlloc_5512_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5494_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_convertNumber___closed__15;
                lean_inc_n(v___x_5489_, 7);
                v___x_5495_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5495_, 0, v___x_5489_);
                lean_ctor_set(v___x_5495_, 1, v___x_5484_);
                v___x_5496_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__7;
                v___x_5497_ =
                    l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__8;
                v___x_5498_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5498_, 0, v___x_5489_);
                lean_ctor_set(v___x_5498_, 1, v___x_5497_);
                v___x_5499_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9_once), _init_l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__9);
                v___x_5500_ = l_Array_append___redArg(v___x_5499_, v___x_5486_);
                lean_dec_ref(v___x_5486_);
                v___x_5501_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5501_, 0, v___x_5489_);
                lean_ctor_set(v___x_5501_, 1, v___x_5494_);
                lean_ctor_set(v___x_5501_, 2, v___x_5500_);
                v___x_5502_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__10;
                v___x_5503_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5503_, 0, v___x_5489_);
                lean_ctor_set(v___x_5503_, 1, v___x_5502_);
                v___x_5504_ = l_Lean_Syntax_node3(
                    v___x_5489_,
                    v___x_5496_,
                    v___x_5498_,
                    v___x_5501_,
                    v___x_5503_,
                );
                v___x_5505_ = l_Lean_Syntax_node3(
                    v___x_5489_,
                    v___x_5494_,
                    v___y_5488_,
                    v___x_5495_,
                    v___x_5504_,
                );
                v___x_5506_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___closed__11;
                v___x_5507_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5507_, 0, v___x_5489_);
                lean_ctor_set(v___x_5507_, 1, v___x_5506_);
                v___x_5508_ = l_Lean_Syntax_node3(
                    v___x_5489_,
                    v___x_5490_,
                    v___x_5493_,
                    v___x_5505_,
                    v___x_5507_,
                );
                if v_isShared_5482_ == 0 {
                    lean_ctor_set(v___x_5481_, 0, v___x_5508_);
                    v___x_5510_ = v___x_5481_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5508_);
                    lean_ctor_set(v_reuseFailAlloc_5511_, 1, v_a_5479_);
                    v___x_5510_ = v_reuseFailAlloc_5511_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5510_;
            }
            6 => {
                if v_isShared_5537_ == 0 {
                    v___x_5539_ = v___x_5536_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5533_);
                    lean_ctor_set(v_reuseFailAlloc_5540_, 1, v_a_5534_);
                    v___x_5539_ = v_reuseFailAlloc_5540_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat___boxed(
    mut v_fmt_5544_: *mut LeanObject,
    mut v_config_5545_: *mut LeanObject,
    mut v_a_5546_: *mut LeanObject,
    mut v_a_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5548_: *mut LeanObject = core::ptr::null_mut();
    v_res_5548_ = l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(
        v_fmt_5544_,
        v_config_5545_,
        v_a_5546_,
        v_a_5547_,
    );
    lean_dec_ref(v_a_5546_);
    lean_dec(v_fmt_5544_);
    return v_res_5548_;
}
pub unsafe fn l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1(
    mut v_x_5549_: *mut LeanObject,
    mut v_a_5550_: *mut LeanObject,
    mut v_a_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: u8 = 0;
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmt_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5572_: u8 = 0;
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5552_ = l_Std_Time_termDatespec_x28___x29___closed__1;
                lean_inc(v_x_5549_);
                v___x_5553_ = l_Lean_Syntax_isOfKind(v_x_5549_, v___x_5552_);
                if v___x_5553_ == 0 {
                    lean_dec(v_x_5549_);
                    v___x_5554_ = lean_box(1);
                    v___x_5555_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5555_, 0, v___x_5554_);
                    lean_ctor_set(v___x_5555_, 1, v_a_5551_);
                    return v___x_5555_;
                } else {
                    v___x_5556_ = lean_unsigned_to_nat(1);
                    v_fmt_5557_ = l_Lean_Syntax_getArg(v_x_5549_, v___x_5556_);
                    lean_dec(v_x_5549_);
                    v___x_5558_ = l_Std_Time_termDatespec_x28___x29___closed__7;
                    lean_inc(v_fmt_5557_);
                    v___x_5559_ = l_Lean_Syntax_isOfKind(v_fmt_5557_, v___x_5558_);
                    if v___x_5559_ == 0 {
                        lean_dec(v_fmt_5557_);
                        v___x_5560_ = lean_box(1);
                        v___x_5561_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5561_, 0, v___x_5560_);
                        lean_ctor_set(v___x_5561_, 1, v_a_5551_);
                        return v___x_5561_;
                    } else {
                        v___x_5562_ = lean_box(0);
                        v___x_5563_ =
                            l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(
                                v_fmt_5557_,
                                v___x_5562_,
                                v_a_5550_,
                                v_a_5551_,
                            );
                        lean_dec(v_fmt_5557_);
                        if lean_obj_tag(v___x_5563_) == 0 {
                            v_a_5564_ = lean_ctor_get(v___x_5563_, 0);
                            v_a_5565_ = lean_ctor_get(v___x_5563_, 1);
                            v_isSharedCheck_5572_ = (!lean_is_exclusive(v___x_5563_)) as u8;
                            if v_isSharedCheck_5572_ == 0 {
                                v___x_5567_ = v___x_5563_;
                                v_isShared_5568_ = v_isSharedCheck_5572_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5565_);
                                lean_inc(v_a_5564_);
                                lean_dec(v___x_5563_);
                                v___x_5567_ = lean_box(0);
                                v_isShared_5568_ = v_isSharedCheck_5572_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5573_ = lean_ctor_get(v___x_5563_, 0);
                            v_a_5574_ = lean_ctor_get(v___x_5563_, 1);
                            v_isSharedCheck_5581_ = (!lean_is_exclusive(v___x_5563_)) as u8;
                            if v_isSharedCheck_5581_ == 0 {
                                v___x_5576_ = v___x_5563_;
                                v_isShared_5577_ = v_isSharedCheck_5581_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5574_);
                                lean_inc(v_a_5573_);
                                lean_dec(v___x_5563_);
                                v___x_5576_ = lean_box(0);
                                v_isShared_5577_ = v_isSharedCheck_5581_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5568_ == 0 {
                    v___x_5570_ = v___x_5567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5564_);
                    lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_a_5565_);
                    v___x_5570_ = v_reuseFailAlloc_5571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5570_;
            }
            3 => {
                if v_isShared_5577_ == 0 {
                    v___x_5579_ = v___x_5576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5573_);
                    lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_a_5574_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1___boxed(
    mut v_x_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5585_: *mut LeanObject = core::ptr::null_mut();
    v_res_5585_ = l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x29__1(v_x_5582_, v_a_5583_, v_a_5584_);
    lean_dec_ref(v_a_5583_);
    return v_res_5585_;
}
pub unsafe fn l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1(
    mut v_x_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: u8 = 0;
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmt_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5607_: u8 = 0;
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5611_: u8 = 0;
    let mut v_a_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5616_: u8 = 0;
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5589_ = l_Std_Time_termDatespec_x28___x2c___x29___closed__1;
                lean_inc(v_x_5586_);
                v___x_5590_ = l_Lean_Syntax_isOfKind(v_x_5586_, v___x_5589_);
                if v___x_5590_ == 0 {
                    lean_dec(v_x_5586_);
                    v___x_5591_ = lean_box(1);
                    v___x_5592_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5592_, 0, v___x_5591_);
                    lean_ctor_set(v___x_5592_, 1, v_a_5588_);
                    return v___x_5592_;
                } else {
                    v___x_5593_ = lean_unsigned_to_nat(1);
                    v_fmt_5594_ = l_Lean_Syntax_getArg(v_x_5586_, v___x_5593_);
                    v___x_5595_ = l_Std_Time_termDatespec_x28___x29___closed__7;
                    lean_inc(v_fmt_5594_);
                    v___x_5596_ = l_Lean_Syntax_isOfKind(v_fmt_5594_, v___x_5595_);
                    if v___x_5596_ == 0 {
                        lean_dec(v_fmt_5594_);
                        lean_dec(v_x_5586_);
                        v___x_5597_ = lean_box(1);
                        v___x_5598_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5598_, 0, v___x_5597_);
                        lean_ctor_set(v___x_5598_, 1, v_a_5588_);
                        return v___x_5598_;
                    } else {
                        v___x_5599_ = lean_unsigned_to_nat(3);
                        v_config_5600_ = l_Lean_Syntax_getArg(v_x_5586_, v___x_5599_);
                        lean_dec(v_x_5586_);
                        v___x_5601_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5601_, 0, v_config_5600_);
                        v___x_5602_ =
                            l___private_Std_Time_Notation_Spec_0__Std_Time_formatStringToFormat(
                                v_fmt_5594_,
                                v___x_5601_,
                                v_a_5587_,
                                v_a_5588_,
                            );
                        lean_dec(v_fmt_5594_);
                        if lean_obj_tag(v___x_5602_) == 0 {
                            v_a_5603_ = lean_ctor_get(v___x_5602_, 0);
                            v_a_5604_ = lean_ctor_get(v___x_5602_, 1);
                            v_isSharedCheck_5611_ = (!lean_is_exclusive(v___x_5602_)) as u8;
                            if v_isSharedCheck_5611_ == 0 {
                                v___x_5606_ = v___x_5602_;
                                v_isShared_5607_ = v_isSharedCheck_5611_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5604_);
                                lean_inc(v_a_5603_);
                                lean_dec(v___x_5602_);
                                v___x_5606_ = lean_box(0);
                                v_isShared_5607_ = v_isSharedCheck_5611_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5612_ = lean_ctor_get(v___x_5602_, 0);
                            v_a_5613_ = lean_ctor_get(v___x_5602_, 1);
                            v_isSharedCheck_5620_ = (!lean_is_exclusive(v___x_5602_)) as u8;
                            if v_isSharedCheck_5620_ == 0 {
                                v___x_5615_ = v___x_5602_;
                                v_isShared_5616_ = v_isSharedCheck_5620_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5613_);
                                lean_inc(v_a_5612_);
                                lean_dec(v___x_5602_);
                                v___x_5615_ = lean_box(0);
                                v_isShared_5616_ = v_isSharedCheck_5620_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5607_ == 0 {
                    v___x_5609_ = v___x_5606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5603_);
                    lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_a_5604_);
                    v___x_5609_ = v_reuseFailAlloc_5610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5609_;
            }
            3 => {
                if v_isShared_5616_ == 0 {
                    v___x_5618_ = v___x_5615_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5612_);
                    lean_ctor_set(v_reuseFailAlloc_5619_, 1, v_a_5613_);
                    v___x_5618_ = v_reuseFailAlloc_5619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1___boxed(
    mut v_x_5621_: *mut LeanObject,
    mut v_a_5622_: *mut LeanObject,
    mut v_a_5623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5624_: *mut LeanObject = core::ptr::null_mut();
    v_res_5624_ = l_Std_Time___aux__Std__Time__Notation__Spec______macroRules__Std__Time__termDatespec_x28___x2c___x29__1(v_x_5621_, v_a_5622_, v_a_5623_);
    lean_dec_ref(v_a_5622_);
    return v_res_5624_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Notation_Spec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Notation_Spec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Notation_Spec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Format_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Notation_Spec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Notation_Spec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Notation_Spec(builtin);
}
