// Lean compiler output
// Module: Lean.Data.Format
// Imports: Lean.Data.Options Init.Data.Format.Instances
use crate::ffi::{lean_nat_to_int, lean_string_length};
use crate::r#gen::Init::Data::Format::Basic::{
    l_Std_Format_defIndent, l_Std_Format_defUnicode, l_Std_Format_defWidth, l_Std_Format_pretty,
};
use crate::r#gen::Init::Data::Format::Instances::{
    initialize_Init_Data_Format_Instances, runtime_initialize_Init_Data_Format_Instances,
};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
pub static l_Std_Format_getWidth___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 111, 114, 109, 97, 116, 0],
    };
static mut l_Std_Format_getWidth___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Format_getWidth___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [119, 105, 100, 116, 104, 0],
    };
static mut l_Std_Format_getWidth___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getWidth___closed__1_value) as *mut leanh::LeanObject;
static l_Std_Format_getWidth___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value)
                as *mut leanh::LeanObject,
            23689666010326313 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Format_getWidth___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getWidth___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Format_getWidth___closed__1_value)
                as *mut leanh::LeanObject,
            2226843053881947362 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Format_getWidth___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getWidth___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Format_getIndent___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 100, 101, 110, 116, 0],
    };
static mut l_Std_Format_getIndent___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getIndent___closed__0_value) as *mut leanh::LeanObject;
static l_Std_Format_getIndent___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value)
                as *mut leanh::LeanObject,
            23689666010326313 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Format_getIndent___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getIndent___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Format_getIndent___closed__0_value)
                as *mut leanh::LeanObject,
            14758375440679154132 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Format_getIndent___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getIndent___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Format_getUnicode___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [117, 110, 105, 99, 111, 100, 101, 0],
    };
static mut l_Std_Format_getUnicode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getUnicode___closed__0_value) as *mut leanh::LeanObject;
static l_Std_Format_getUnicode___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value)
                as *mut leanh::LeanObject,
            23689666010326313 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Format_getUnicode___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Format_getUnicode___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Format_getUnicode___closed__0_value)
                as *mut leanh::LeanObject,
            894308731169599158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Format_getUnicode___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_getUnicode___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 100, 101, 110, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 111, 114, 109, 97, 116, 0]};
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12875137807382502537 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value) as *mut leanh::LeanObject,1849148449987069507 as *mut leanh::LeanObject] };
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getWidth___closed__1_value) as *mut leanh::LeanObject,10408052456244380016 as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Std_Format_format_width: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [117, 110, 105, 99, 111, 100, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12875137807382502537 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value) as *mut leanh::LeanObject,1849148449987069507 as *mut leanh::LeanObject] };
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getUnicode___closed__0_value) as *mut leanh::LeanObject,6222756312481965892 as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Std_Format_format_unicode: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12875137807382502537 as *mut leanh::LeanObject] };
static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getWidth___closed__0_value) as *mut leanh::LeanObject,1849148449987069507 as *mut leanh::LeanObject] };
pub static l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Format_getIndent___closed__0_value) as *mut leanh::LeanObject,6461048213453430406 as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Std_Format_format_indent: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToFormatName__lean___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToFormatName__lean___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToFormatName__lean___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatName__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToFormatName__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatName__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__4_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___lam__0___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToFormatDataValue___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToFormatDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToFormatDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToFormatDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_instToFormatProdNameDataValue___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatProdNameDataValue___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToFormatProdNameDataValue___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToFormatProdNameDataValue___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_instToFormatProdNameDataValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToFormatProdNameDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatProdNameDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToFormatProdNameDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatProdNameDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_formatKVMap___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Lean_formatKVMap___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_formatKVMap___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_formatKVMap___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lean_formatKVMap___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_formatKVMap___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_formatKVMap___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_formatKVMap___closed__3_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_formatKVMap___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_formatKVMap___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_formatKVMap___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_formatKVMap___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_formatKVMap___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_formatKVMap___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_formatKVMap___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lean_formatKVMap___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_formatKVMap___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_formatKVMap___closed__3_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lean_formatKVMap___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatKVMap___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_instToFormatKVMap___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_formatKVMap as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToFormatKVMap___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatKVMap___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToFormatKVMap: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToFormatKVMap___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Format_getWidth(
    mut v_o_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_621_ = leanh::lean_ctor_get(v_o_620_, 0);
    v___x_622_ = l_Std_Format_getWidth___closed__2;
    v___x_623_ = l_Std_Format_defWidth;
    v___x_624_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_621_, v___x_622_,
        );
    if leanh::lean_obj_tag(v___x_624_) == 0 {
        return v___x_623_;
    } else {
        let mut v_val_625_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_625_ = leanh::lean_ctor_get(v___x_624_, 0);
        leanh::lean_inc(v_val_625_);
        leanh::lean_dec_ref_known(v___x_624_, 1);
        if leanh::lean_obj_tag(v_val_625_) == 3 {
            let mut v_v_626_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_626_ = leanh::lean_ctor_get(v_val_625_, 0);
            leanh::lean_inc(v_v_626_);
            leanh::lean_dec_ref_known(v_val_625_, 1);
            return v_v_626_;
        } else {
            leanh::lean_dec(v_val_625_);
            return v___x_623_;
        }
    }
}
pub unsafe fn l_Std_Format_getWidth___boxed(
    mut v_o_627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_628_ = l_Std_Format_getWidth(v_o_627_);
    leanh::lean_dec_ref(v_o_627_);
    return v_res_628_;
}
pub unsafe fn l_Std_Format_getIndent(
    mut v_o_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_634_ = leanh::lean_ctor_get(v_o_633_, 0);
    v___x_635_ = l_Std_Format_getIndent___closed__1;
    v___x_636_ = l_Std_Format_defIndent;
    v___x_637_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_634_, v___x_635_,
        );
    if leanh::lean_obj_tag(v___x_637_) == 0 {
        return v___x_636_;
    } else {
        let mut v_val_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_638_ = leanh::lean_ctor_get(v___x_637_, 0);
        leanh::lean_inc(v_val_638_);
        leanh::lean_dec_ref_known(v___x_637_, 1);
        if leanh::lean_obj_tag(v_val_638_) == 3 {
            let mut v_v_639_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_639_ = leanh::lean_ctor_get(v_val_638_, 0);
            leanh::lean_inc(v_v_639_);
            leanh::lean_dec_ref_known(v_val_638_, 1);
            return v_v_639_;
        } else {
            leanh::lean_dec(v_val_638_);
            return v___x_636_;
        }
    }
}
pub unsafe fn l_Std_Format_getIndent___boxed(
    mut v_o_640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Std_Format_getIndent(v_o_640_);
    leanh::lean_dec_ref(v_o_640_);
    return v_res_641_;
}
pub unsafe fn l_Std_Format_getUnicode(mut v_o_646_: *mut leanh::LeanObject) -> u8 {
    let mut v_map_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_647_ = leanh::lean_ctor_get(v_o_646_, 0);
    v___x_648_ = l_Std_Format_getUnicode___closed__1;
    v___x_649_ = l_Std_Format_defUnicode;
    v___x_650_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_647_, v___x_648_,
        );
    if leanh::lean_obj_tag(v___x_650_) == 0 {
        return v___x_649_;
    } else {
        let mut v_val_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_651_ = leanh::lean_ctor_get(v___x_650_, 0);
        leanh::lean_inc(v_val_651_);
        leanh::lean_dec_ref_known(v___x_650_, 1);
        if leanh::lean_obj_tag(v_val_651_) == 1 {
            let mut v_v_652_: u8 = 0;
            v_v_652_ = leanh::lean_ctor_get_uint8(v_val_651_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_651_, 0);
            return v_v_652_;
        } else {
            leanh::lean_dec(v_val_651_);
            return v___x_649_;
        }
    }
}
pub unsafe fn l_Std_Format_getUnicode___boxed(
    mut v_o_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_654_: u8 = 0;
    let mut v_r_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_654_ = l_Std_Format_getUnicode(v_o_653_);
    leanh::lean_dec_ref(v_o_653_);
    v_r_655_ = leanh::lean_box((v_res_654_) as usize);
    return v_r_655_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(
    mut v_name_656_: *mut leanh::LeanObject,
    mut v_decl_657_: *mut leanh::LeanObject,
    mut v_ref_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_unused_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_660_ = leanh::lean_ctor_get(v_decl_657_, 0);
                v_descr_661_ = leanh::lean_ctor_get(v_decl_657_, 1);
                v_deprecation_x3f_662_ = leanh::lean_ctor_get(v_decl_657_, 2);
                leanh::lean_inc(v_defValue_660_);
                v___x_663_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_663_, 0, v_defValue_660_);
                leanh::lean_inc(v_deprecation_x3f_662_);
                leanh::lean_inc_ref(v_descr_661_);
                leanh::lean_inc_n(v_name_656_, 2);
                v___x_664_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_664_, 0, v_name_656_);
                leanh::lean_ctor_set(v___x_664_, 1, v_ref_658_);
                leanh::lean_ctor_set(v___x_664_, 2, v___x_663_);
                leanh::lean_ctor_set(v___x_664_, 3, v_descr_661_);
                leanh::lean_ctor_set(v___x_664_, 4, v_deprecation_x3f_662_);
                v___x_665_ = lean_register_option(v_name_656_, v___x_664_);
                if leanh::lean_obj_tag(v___x_665_) == 0 {
                    v_isSharedCheck_673_ = (!leanh::lean_is_exclusive(v___x_665_)) as u8;
                    if v_isSharedCheck_673_ == 0 {
                        v_unused_674_ = leanh::lean_ctor_get(v___x_665_, 0);
                        leanh::lean_dec(v_unused_674_);
                        v___x_667_ = v___x_665_;
                        v_isShared_668_ = v_isSharedCheck_673_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_665_);
                        v___x_667_ = leanh::lean_box(0);
                        v_isShared_668_ = v_isSharedCheck_673_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_656_);
                    v_a_675_ = leanh::lean_ctor_get(v___x_665_, 0);
                    v_isSharedCheck_682_ = (!leanh::lean_is_exclusive(v___x_665_)) as u8;
                    if v_isSharedCheck_682_ == 0 {
                        v___x_677_ = v___x_665_;
                        v_isShared_678_ = v_isSharedCheck_682_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_675_);
                        leanh::lean_dec(v___x_665_);
                        v___x_677_ = leanh::lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_682_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_660_);
                v___x_669_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_669_, 0, v_name_656_);
                leanh::lean_ctor_set(v___x_669_, 1, v_defValue_660_);
                if v_isShared_668_ == 0 {
                    leanh::lean_ctor_set(v___x_667_, 0, v___x_669_);
                    v___x_671_ = v___x_667_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
                    v___x_671_ = v_reuseFailAlloc_672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_671_;
            }
            3 => {
                if v_isShared_678_ == 0 {
                    v___x_680_ = v___x_677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
                    v___x_680_ = v_reuseFailAlloc_681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_683_: *mut leanh::LeanObject,
    mut v_decl_684_: *mut leanh::LeanObject,
    mut v_ref_685_: *mut leanh::LeanObject,
    mut v_a_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_683_, v_decl_684_, v_ref_685_);
    leanh::lean_dec_ref(v_decl_684_);
    return v_res_687_;
}
pub unsafe fn _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = leanh::lean_box(0);
    v___x_690_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
    v___x_691_ = l_Std_Format_defWidth;
    v___x_692_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
    leanh::lean_ctor_set(v___x_692_, 1, v___x_690_);
    leanh::lean_ctor_set(v___x_692_, 2, v___x_689_);
    return v___x_692_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_701_ = l_Std_Format_getWidth___closed__2;
    v___x_702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_), core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once), _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_);
    v___x_703_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
    v___x_704_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_701_, v___x_702_, v___x_703_);
    return v___x_704_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(
    mut v_a_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_706_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
    return v_res_706_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(
    mut v_name_707_: *mut leanh::LeanObject,
    mut v_decl_708_: *mut leanh::LeanObject,
    mut v_ref_709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_unused_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_711_ = leanh::lean_ctor_get(v_decl_708_, 0);
                v_descr_712_ = leanh::lean_ctor_get(v_decl_708_, 1);
                v_deprecation_x3f_713_ = leanh::lean_ctor_get(v_decl_708_, 2);
                v___x_714_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_715_ = (leanh::lean_unbox(v_defValue_711_) as u8);
                leanh::lean_ctor_set_uint8(v___x_714_, 0 as u32, v___x_715_);
                leanh::lean_inc(v_deprecation_x3f_713_);
                leanh::lean_inc_ref(v_descr_712_);
                leanh::lean_inc_n(v_name_707_, 2);
                v___x_716_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_716_, 0, v_name_707_);
                leanh::lean_ctor_set(v___x_716_, 1, v_ref_709_);
                leanh::lean_ctor_set(v___x_716_, 2, v___x_714_);
                leanh::lean_ctor_set(v___x_716_, 3, v_descr_712_);
                leanh::lean_ctor_set(v___x_716_, 4, v_deprecation_x3f_713_);
                v___x_717_ = lean_register_option(v_name_707_, v___x_716_);
                if leanh::lean_obj_tag(v___x_717_) == 0 {
                    v_isSharedCheck_725_ = (!leanh::lean_is_exclusive(v___x_717_)) as u8;
                    if v_isSharedCheck_725_ == 0 {
                        v_unused_726_ = leanh::lean_ctor_get(v___x_717_, 0);
                        leanh::lean_dec(v_unused_726_);
                        v___x_719_ = v___x_717_;
                        v_isShared_720_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_717_);
                        v___x_719_ = leanh::lean_box(0);
                        v_isShared_720_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_707_);
                    v_a_727_ = leanh::lean_ctor_get(v___x_717_, 0);
                    v_isSharedCheck_734_ = (!leanh::lean_is_exclusive(v___x_717_)) as u8;
                    if v_isSharedCheck_734_ == 0 {
                        v___x_729_ = v___x_717_;
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_727_);
                        leanh::lean_dec(v___x_717_);
                        v___x_729_ = leanh::lean_box(0);
                        v_isShared_730_ = v_isSharedCheck_734_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_711_);
                v___x_721_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_721_, 0, v_name_707_);
                leanh::lean_ctor_set(v___x_721_, 1, v_defValue_711_);
                if v_isShared_720_ == 0 {
                    leanh::lean_ctor_set(v___x_719_, 0, v___x_721_);
                    v___x_723_ = v___x_719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
                    v___x_723_ = v_reuseFailAlloc_724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_723_;
            }
            3 => {
                if v_isShared_730_ == 0 {
                    v___x_732_ = v___x_729_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
                    v___x_732_ = v_reuseFailAlloc_733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_735_: *mut leanh::LeanObject,
    mut v_decl_736_: *mut leanh::LeanObject,
    mut v_ref_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_735_, v_decl_736_, v_ref_737_);
    leanh::lean_dec_ref(v_decl_736_);
    return v_res_739_;
}
pub unsafe fn _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: u8 = 0;
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = leanh::lean_box(0);
    v___x_742_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_;
    v___x_743_ = l_Std_Format_defUnicode;
    v___x_744_ = leanh::lean_box((v___x_743_) as usize);
    v___x_745_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_745_, 0, v___x_744_);
    leanh::lean_ctor_set(v___x_745_, 1, v___x_742_);
    leanh::lean_ctor_set(v___x_745_, 2, v___x_741_);
    return v___x_745_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Std_Format_getUnicode___closed__1;
    v___x_753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_), core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once), _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_);
    v___x_754_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_;
    v___x_755_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v___x_752_, v___x_753_, v___x_754_);
    return v___x_755_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(
    mut v_a_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
    return v_res_757_;
}
pub unsafe fn _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = leanh::lean_box(0);
    v___x_759_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
    v___x_760_ = l_Std_Format_defIndent;
    v___x_761_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_761_, 0, v___x_760_);
    leanh::lean_ctor_set(v___x_761_, 1, v___x_759_);
    leanh::lean_ctor_set(v___x_761_, 2, v___x_758_);
    return v___x_761_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = l_Std_Format_getIndent___closed__1;
    v___x_769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_), core::ptr::addr_of_mut!(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once), _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_);
    v___x_770_ = l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_;
    v___x_771_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_768_, v___x_769_, v___x_770_);
    return v___x_771_;
}
pub unsafe fn l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(
    mut v_a_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
    return v_res_773_;
}
pub unsafe fn l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(
    mut v_opts_774_: *mut leanh::LeanObject,
    mut v_opt_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_776_ = leanh::lean_ctor_get(v_opt_775_, 0);
    v_defValue_777_ = leanh::lean_ctor_get(v_opt_775_, 1);
    v_map_778_ = leanh::lean_ctor_get(v_opts_774_, 0);
    v___x_779_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_778_,
            v_name_776_,
        );
    if leanh::lean_obj_tag(v___x_779_) == 0 {
        leanh::lean_inc(v_defValue_777_);
        return v_defValue_777_;
    } else {
        let mut v_val_780_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_780_ = leanh::lean_ctor_get(v___x_779_, 0);
        leanh::lean_inc(v_val_780_);
        leanh::lean_dec_ref_known(v___x_779_, 1);
        if leanh::lean_obj_tag(v_val_780_) == 3 {
            let mut v_v_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_781_ = leanh::lean_ctor_get(v_val_780_, 0);
            leanh::lean_inc(v_v_781_);
            leanh::lean_dec_ref_known(v_val_780_, 1);
            return v_v_781_;
        } else {
            leanh::lean_dec(v_val_780_);
            leanh::lean_inc(v_defValue_777_);
            return v_defValue_777_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0___boxed(
    mut v_opts_782_: *mut leanh::LeanObject,
    mut v_opt_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_opts_782_, v_opt_783_);
    leanh::lean_dec_ref(v_opt_783_);
    leanh::lean_dec_ref(v_opts_782_);
    return v_res_784_;
}
pub unsafe fn l_Std_Format_pretty_x27(
    mut v_f_785_: *mut leanh::LeanObject,
    mut v_o_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = l_Std_Format_format_width;
    v___x_788_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_o_786_, v___x_787_);
    v___x_789_ = leanh::lean_unsigned_to_nat(0);
    v___x_790_ = l_Std_Format_pretty(v_f_785_, v___x_788_, v___x_789_, v___x_789_);
    leanh::lean_dec(v___x_788_);
    return v___x_790_;
}
pub unsafe fn l_Std_Format_pretty_x27___boxed(
    mut v_f_791_: *mut leanh::LeanObject,
    mut v_o_792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_793_ = l_Std_Format_pretty_x27(v_f_791_, v_o_792_);
    leanh::lean_dec_ref(v_o_792_);
    return v_res_793_;
}
pub unsafe fn l_Lean_instToFormatName__lean___lam__0(
    mut v_n_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = 1;
    v___x_796_ = l_Lean_Name_toString(v_n_794_, v___x_795_);
    v___x_797_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
    return v___x_797_;
}
pub unsafe fn l_Lean_instToFormatDataValue___lam__0(
    mut v_x_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_813_: u8 = 0;
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut v_v_819_: u8 = 0;
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_825_: u8 = 0;
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v_v_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_842_: u8 = 0;
    let mut v_v_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_846_: u8 = 0;
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_v_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_809_) {
                0 => {
                    v_v_810_ = leanh::lean_ctor_get(v_x_809_, 0);
                    v_isSharedCheck_818_ = (!leanh::lean_is_exclusive(v_x_809_)) as u8;
                    if v_isSharedCheck_818_ == 0 {
                        v___x_812_ = v_x_809_;
                        v_isShared_813_ = v_isSharedCheck_818_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_810_);
                        leanh::lean_dec(v_x_809_);
                        v___x_812_ = leanh::lean_box(0);
                        v_isShared_813_ = v_isSharedCheck_818_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_v_819_ = leanh::lean_ctor_get_uint8(v_x_809_, 0 as u32);
                    leanh::lean_dec_ref_known(v_x_809_, 0);
                    if v_v_819_ == 0 {
                        v___x_820_ = l_Lean_instToFormatDataValue___lam__0___closed__1;
                        return v___x_820_;
                    } else {
                        v___x_821_ = l_Lean_instToFormatDataValue___lam__0___closed__3;
                        return v___x_821_;
                    }
                }
                2 => {
                    v_v_822_ = leanh::lean_ctor_get(v_x_809_, 0);
                    v_isSharedCheck_833_ = (!leanh::lean_is_exclusive(v_x_809_)) as u8;
                    if v_isSharedCheck_833_ == 0 {
                        v___x_824_ = v_x_809_;
                        v_isShared_825_ = v_isSharedCheck_833_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_822_);
                        leanh::lean_dec(v_x_809_);
                        v___x_824_ = leanh::lean_box(0);
                        v_isShared_825_ = v_isSharedCheck_833_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_v_834_ = leanh::lean_ctor_get(v_x_809_, 0);
                    v_isSharedCheck_842_ = (!leanh::lean_is_exclusive(v_x_809_)) as u8;
                    if v_isSharedCheck_842_ == 0 {
                        v___x_836_ = v_x_809_;
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_834_);
                        leanh::lean_dec(v_x_809_);
                        v___x_836_ = leanh::lean_box(0);
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_v_843_ = leanh::lean_ctor_get(v_x_809_, 0);
                    v_isSharedCheck_851_ = (!leanh::lean_is_exclusive(v_x_809_)) as u8;
                    if v_isSharedCheck_851_ == 0 {
                        v___x_845_ = v_x_809_;
                        v_isShared_846_ = v_isSharedCheck_851_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_843_);
                        leanh::lean_dec(v_x_809_);
                        v___x_845_ = leanh::lean_box(0);
                        v_isShared_846_ = v_isSharedCheck_851_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_v_852_ = leanh::lean_ctor_get(v_x_809_, 0);
                    leanh::lean_inc(v_v_852_);
                    leanh::lean_dec_ref_known(v_x_809_, 1);
                    v___x_853_ = leanh::lean_box(0);
                    v___x_854_ = 0;
                    v___x_855_ = l_Lean_Syntax_formatStx(v_v_852_, v___x_853_, v___x_854_);
                    return v___x_855_;
                }
            },
            1 => {
                v___x_814_ = l_String_quote(v_v_810_);
                if v_isShared_813_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_812_, 3);
                    leanh::lean_ctor_set(v___x_812_, 0, v___x_814_);
                    v___x_816_ = v___x_812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_817_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
                    v___x_816_ = v_reuseFailAlloc_817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_816_;
            }
            3 => {
                v___x_826_ = l_Lean_instToFormatDataValue___lam__0___closed__5;
                v___x_827_ = 1;
                v___x_828_ = l_Lean_Name_toString(v_v_822_, v___x_827_);
                if v_isShared_825_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_824_, 3);
                    leanh::lean_ctor_set(v___x_824_, 0, v___x_828_);
                    v___x_830_ = v___x_824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
                    v___x_830_ = v_reuseFailAlloc_832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_831_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_831_, 0, v___x_826_);
                leanh::lean_ctor_set(v___x_831_, 1, v___x_830_);
                return v___x_831_;
            }
            5 => {
                v___x_838_ = l_Nat_reprFast(v_v_834_);
                if v_isShared_837_ == 0 {
                    leanh::lean_ctor_set(v___x_836_, 0, v___x_838_);
                    v___x_840_ = v___x_836_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_841_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
                    v___x_840_ = v_reuseFailAlloc_841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_840_;
            }
            7 => {
                v___x_847_ = l_Int_repr(v_v_843_);
                leanh::lean_dec(v_v_843_);
                if v_isShared_846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_845_, 3);
                    leanh::lean_ctor_set(v___x_845_, 0, v___x_847_);
                    v___x_849_ = v___x_845_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
                    v___x_849_ = v_reuseFailAlloc_850_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToFormatProdNameDataValue___lam__0(
    mut v_x_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_v_883_: u8 = 0;
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_899_: u8 = 0;
    let mut v_v_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut v_v_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_919_: u8 = 0;
    let mut v_v_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_862_ = leanh::lean_ctor_get(v_x_861_, 0);
                v_snd_863_ = leanh::lean_ctor_get(v_x_861_, 1);
                v_isSharedCheck_926_ = (!leanh::lean_is_exclusive(v_x_861_)) as u8;
                if v_isSharedCheck_926_ == 0 {
                    v___x_865_ = v_x_861_;
                    v_isShared_866_ = v_isSharedCheck_926_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_863_);
                    leanh::lean_inc(v_fst_862_);
                    leanh::lean_dec(v_x_861_);
                    v___x_865_ = leanh::lean_box(0);
                    v_isShared_866_ = v_isSharedCheck_926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_867_ = 1;
                v___x_868_ = l_Lean_Name_toString(v_fst_862_, v___x_867_);
                v___x_869_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_869_, 0, v___x_868_);
                v___x_870_ = l_Lean_instToFormatProdNameDataValue___lam__0___closed__1;
                if v_isShared_866_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_865_, 5);
                    leanh::lean_ctor_set(v___x_865_, 1, v___x_870_);
                    leanh::lean_ctor_set(v___x_865_, 0, v___x_869_);
                    v___x_872_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_925_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_870_);
                    v___x_872_ = v_reuseFailAlloc_925_;
                    state = 2;
                    continue;
                }
            }
            2 => match leanh::lean_obj_tag(v_snd_863_) {
                0 => {
                    v_v_873_ = leanh::lean_ctor_get(v_snd_863_, 0);
                    v_isSharedCheck_882_ = (!leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_882_ == 0 {
                        v___x_875_ = v_snd_863_;
                        v_isShared_876_ = v_isSharedCheck_882_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_873_);
                        leanh::lean_dec(v_snd_863_);
                        v___x_875_ = leanh::lean_box(0);
                        v_isShared_876_ = v_isSharedCheck_882_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_v_883_ = leanh::lean_ctor_get_uint8(v_snd_863_, 0 as u32);
                    leanh::lean_dec_ref_known(v_snd_863_, 0);
                    if v_v_883_ == 0 {
                        v___x_884_ = l_Lean_instToFormatDataValue___lam__0___closed__1;
                        v___x_885_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_885_, 0, v___x_872_);
                        leanh::lean_ctor_set(v___x_885_, 1, v___x_884_);
                        return v___x_885_;
                    } else {
                        v___x_886_ = l_Lean_instToFormatDataValue___lam__0___closed__3;
                        v___x_887_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_887_, 0, v___x_872_);
                        leanh::lean_ctor_set(v___x_887_, 1, v___x_886_);
                        return v___x_887_;
                    }
                }
                2 => {
                    v_v_888_ = leanh::lean_ctor_get(v_snd_863_, 0);
                    v_isSharedCheck_899_ = (!leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_899_ == 0 {
                        v___x_890_ = v_snd_863_;
                        v_isShared_891_ = v_isSharedCheck_899_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_888_);
                        leanh::lean_dec(v_snd_863_);
                        v___x_890_ = leanh::lean_box(0);
                        v_isShared_891_ = v_isSharedCheck_899_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_v_900_ = leanh::lean_ctor_get(v_snd_863_, 0);
                    v_isSharedCheck_909_ = (!leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_909_ == 0 {
                        v___x_902_ = v_snd_863_;
                        v_isShared_903_ = v_isSharedCheck_909_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_900_);
                        leanh::lean_dec(v_snd_863_);
                        v___x_902_ = leanh::lean_box(0);
                        v_isShared_903_ = v_isSharedCheck_909_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_v_910_ = leanh::lean_ctor_get(v_snd_863_, 0);
                    v_isSharedCheck_919_ = (!leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_919_ == 0 {
                        v___x_912_ = v_snd_863_;
                        v_isShared_913_ = v_isSharedCheck_919_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_910_);
                        leanh::lean_dec(v_snd_863_);
                        v___x_912_ = leanh::lean_box(0);
                        v_isShared_913_ = v_isSharedCheck_919_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    v_v_920_ = leanh::lean_ctor_get(v_snd_863_, 0);
                    leanh::lean_inc(v_v_920_);
                    leanh::lean_dec_ref_known(v_snd_863_, 1);
                    v___x_921_ = leanh::lean_box(0);
                    v___x_922_ = 0;
                    v___x_923_ = l_Lean_Syntax_formatStx(v_v_920_, v___x_921_, v___x_922_);
                    v___x_924_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_924_, 0, v___x_872_);
                    leanh::lean_ctor_set(v___x_924_, 1, v___x_923_);
                    return v___x_924_;
                }
            },
            3 => {
                v___x_877_ = l_String_quote(v_v_873_);
                if v_isShared_876_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_875_, 3);
                    leanh::lean_ctor_set(v___x_875_, 0, v___x_877_);
                    v___x_879_ = v___x_875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
                    v___x_879_ = v_reuseFailAlloc_881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_880_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_880_, 0, v___x_872_);
                leanh::lean_ctor_set(v___x_880_, 1, v___x_879_);
                return v___x_880_;
            }
            5 => {
                v___x_892_ = l_Lean_instToFormatDataValue___lam__0___closed__5;
                v___x_893_ = l_Lean_Name_toString(v_v_888_, v___x_867_);
                if v_isShared_891_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_890_, 3);
                    leanh::lean_ctor_set(v___x_890_, 0, v___x_893_);
                    v___x_895_ = v___x_890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_898_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_893_);
                    v___x_895_ = v_reuseFailAlloc_898_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_896_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_896_, 0, v___x_892_);
                leanh::lean_ctor_set(v___x_896_, 1, v___x_895_);
                v___x_897_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_897_, 0, v___x_872_);
                leanh::lean_ctor_set(v___x_897_, 1, v___x_896_);
                return v___x_897_;
            }
            7 => {
                v___x_904_ = l_Nat_reprFast(v_v_900_);
                if v_isShared_903_ == 0 {
                    leanh::lean_ctor_set(v___x_902_, 0, v___x_904_);
                    v___x_906_ = v___x_902_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
                    v___x_906_ = v_reuseFailAlloc_908_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_907_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_907_, 0, v___x_872_);
                leanh::lean_ctor_set(v___x_907_, 1, v___x_906_);
                return v___x_907_;
            }
            9 => {
                v___x_914_ = l_Int_repr(v_v_910_);
                leanh::lean_dec(v_v_910_);
                if v_isShared_913_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_912_, 3);
                    leanh::lean_ctor_set(v___x_912_, 0, v___x_914_);
                    v___x_916_ = v___x_912_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_918_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_914_);
                    v___x_916_ = v_reuseFailAlloc_918_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_917_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_917_, 0, v___x_872_);
                leanh::lean_ctor_set(v___x_917_, 1, v___x_916_);
                return v___x_917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_formatKVMap_spec__1(
    mut v_a_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = lean_nat_to_int(v_a_929_);
    return v___x_930_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(
    mut v_x_931_: *mut leanh::LeanObject,
    mut v_x_932_: *mut leanh::LeanObject,
    mut v_x_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v_fst_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_955_: u8 = 0;
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v_v_964_: u8 = 0;
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut v_v_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_v_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v_v_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut v_isSharedCheck_1021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_933_) == 0 {
                    leanh::lean_dec(v_x_931_);
                    return v_x_932_;
                } else {
                    v_head_934_ = leanh::lean_ctor_get(v_x_933_, 0);
                    v_tail_935_ = leanh::lean_ctor_get(v_x_933_, 1);
                    v_isSharedCheck_1021_ = (!leanh::lean_is_exclusive(v_x_933_)) as u8;
                    if v_isSharedCheck_1021_ == 0 {
                        v___x_937_ = v_x_933_;
                        v_isShared_938_ = v_isSharedCheck_1021_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_935_);
                        leanh::lean_inc(v_head_934_);
                        leanh::lean_dec(v_x_933_);
                        v___x_937_ = leanh::lean_box(0);
                        v_isShared_938_ = v_isSharedCheck_1021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_939_ = leanh::lean_ctor_get(v_head_934_, 0);
                v_snd_940_ = leanh::lean_ctor_get(v_head_934_, 1);
                v_isSharedCheck_1020_ = (!leanh::lean_is_exclusive(v_head_934_)) as u8;
                if v_isSharedCheck_1020_ == 0 {
                    v___x_942_ = v_head_934_;
                    v_isShared_943_ = v_isSharedCheck_1020_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_940_);
                    leanh::lean_inc(v_fst_939_);
                    leanh::lean_dec(v_head_934_);
                    v___x_942_ = leanh::lean_box(0);
                    v_isShared_943_ = v_isSharedCheck_1020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_x_931_);
                if v_isShared_943_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_942_, 5);
                    leanh::lean_ctor_set(v___x_942_, 1, v_x_931_);
                    leanh::lean_ctor_set(v___x_942_, 0, v_x_932_);
                    v___x_945_ = v___x_942_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1019_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_x_932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_x_931_);
                    v___x_945_ = v_reuseFailAlloc_1019_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_946_ = 1;
                v___x_947_ = l_Lean_Name_toString(v_fst_939_, v___x_946_);
                v___x_948_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_948_, 0, v___x_947_);
                v___x_949_ = l_Lean_instToFormatProdNameDataValue___lam__0___closed__1;
                if v_isShared_938_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_937_, 5);
                    leanh::lean_ctor_set(v___x_937_, 1, v___x_949_);
                    leanh::lean_ctor_set(v___x_937_, 0, v___x_948_);
                    v___x_951_ = v___x_937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_949_);
                    v___x_951_ = v_reuseFailAlloc_1018_;
                    state = 4;
                    continue;
                }
            }
            4 => match leanh::lean_obj_tag(v_snd_940_) {
                0 => {
                    v_v_952_ = leanh::lean_ctor_get(v_snd_940_, 0);
                    v_isSharedCheck_963_ = (!leanh::lean_is_exclusive(v_snd_940_)) as u8;
                    if v_isSharedCheck_963_ == 0 {
                        v___x_954_ = v_snd_940_;
                        v_isShared_955_ = v_isSharedCheck_963_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_952_);
                        leanh::lean_dec(v_snd_940_);
                        v___x_954_ = leanh::lean_box(0);
                        v_isShared_955_ = v_isSharedCheck_963_;
                        state = 5;
                        continue;
                    }
                }
                1 => {
                    v_v_964_ = leanh::lean_ctor_get_uint8(v_snd_940_, 0 as u32);
                    leanh::lean_dec_ref_known(v_snd_940_, 0);
                    if v_v_964_ == 0 {
                        v___x_965_ = l_Lean_instToFormatDataValue___lam__0___closed__1;
                        v___x_966_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_966_, 0, v___x_951_);
                        leanh::lean_ctor_set(v___x_966_, 1, v___x_965_);
                        v___x_967_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_967_, 0, v___x_945_);
                        leanh::lean_ctor_set(v___x_967_, 1, v___x_966_);
                        v_x_932_ = v___x_967_;
                        v_x_933_ = v_tail_935_;
                        state = 0;
                        continue;
                    } else {
                        v___x_969_ = l_Lean_instToFormatDataValue___lam__0___closed__3;
                        v___x_970_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_970_, 0, v___x_951_);
                        leanh::lean_ctor_set(v___x_970_, 1, v___x_969_);
                        v___x_971_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_971_, 0, v___x_945_);
                        leanh::lean_ctor_set(v___x_971_, 1, v___x_970_);
                        v_x_932_ = v___x_971_;
                        v_x_933_ = v_tail_935_;
                        state = 0;
                        continue;
                    }
                }
                2 => {
                    v_v_973_ = leanh::lean_ctor_get(v_snd_940_, 0);
                    v_isSharedCheck_986_ = (!leanh::lean_is_exclusive(v_snd_940_)) as u8;
                    if v_isSharedCheck_986_ == 0 {
                        v___x_975_ = v_snd_940_;
                        v_isShared_976_ = v_isSharedCheck_986_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_973_);
                        leanh::lean_dec(v_snd_940_);
                        v___x_975_ = leanh::lean_box(0);
                        v_isShared_976_ = v_isSharedCheck_986_;
                        state = 7;
                        continue;
                    }
                }
                3 => {
                    v_v_987_ = leanh::lean_ctor_get(v_snd_940_, 0);
                    v_isSharedCheck_998_ = (!leanh::lean_is_exclusive(v_snd_940_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_989_ = v_snd_940_;
                        v_isShared_990_ = v_isSharedCheck_998_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_987_);
                        leanh::lean_dec(v_snd_940_);
                        v___x_989_ = leanh::lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_998_;
                        state = 9;
                        continue;
                    }
                }
                4 => {
                    v_v_999_ = leanh::lean_ctor_get(v_snd_940_, 0);
                    v_isSharedCheck_1010_ = (!leanh::lean_is_exclusive(v_snd_940_)) as u8;
                    if v_isSharedCheck_1010_ == 0 {
                        v___x_1001_ = v_snd_940_;
                        v_isShared_1002_ = v_isSharedCheck_1010_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_999_);
                        leanh::lean_dec(v_snd_940_);
                        v___x_1001_ = leanh::lean_box(0);
                        v_isShared_1002_ = v_isSharedCheck_1010_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    v_v_1011_ = leanh::lean_ctor_get(v_snd_940_, 0);
                    leanh::lean_inc(v_v_1011_);
                    leanh::lean_dec_ref_known(v_snd_940_, 1);
                    v___x_1012_ = leanh::lean_box(0);
                    v___x_1013_ = 0;
                    v___x_1014_ = l_Lean_Syntax_formatStx(v_v_1011_, v___x_1012_, v___x_1013_);
                    v___x_1015_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1015_, 0, v___x_951_);
                    leanh::lean_ctor_set(v___x_1015_, 1, v___x_1014_);
                    v___x_1016_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1016_, 0, v___x_945_);
                    leanh::lean_ctor_set(v___x_1016_, 1, v___x_1015_);
                    v_x_932_ = v___x_1016_;
                    v_x_933_ = v_tail_935_;
                    state = 0;
                    continue;
                }
            },
            5 => {
                v___x_956_ = l_String_quote(v_v_952_);
                if v_isShared_955_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_954_, 3);
                    leanh::lean_ctor_set(v___x_954_, 0, v___x_956_);
                    v___x_958_ = v___x_954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_956_);
                    v___x_958_ = v_reuseFailAlloc_962_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_959_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_959_, 0, v___x_951_);
                leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
                v___x_960_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_960_, 0, v___x_945_);
                leanh::lean_ctor_set(v___x_960_, 1, v___x_959_);
                v_x_932_ = v___x_960_;
                v_x_933_ = v_tail_935_;
                state = 0;
                continue;
            }
            7 => {
                v___x_977_ = l_Lean_instToFormatDataValue___lam__0___closed__5;
                v___x_978_ = l_Lean_Name_toString(v_v_973_, v___x_946_);
                if v_isShared_976_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_975_, 3);
                    leanh::lean_ctor_set(v___x_975_, 0, v___x_978_);
                    v___x_980_ = v___x_975_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_978_);
                    v___x_980_ = v_reuseFailAlloc_985_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_981_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_981_, 0, v___x_977_);
                leanh::lean_ctor_set(v___x_981_, 1, v___x_980_);
                v___x_982_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_982_, 0, v___x_951_);
                leanh::lean_ctor_set(v___x_982_, 1, v___x_981_);
                v___x_983_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_983_, 0, v___x_945_);
                leanh::lean_ctor_set(v___x_983_, 1, v___x_982_);
                v_x_932_ = v___x_983_;
                v_x_933_ = v_tail_935_;
                state = 0;
                continue;
            }
            9 => {
                v___x_991_ = l_Nat_reprFast(v_v_987_);
                if v_isShared_990_ == 0 {
                    leanh::lean_ctor_set(v___x_989_, 0, v___x_991_);
                    v___x_993_ = v___x_989_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_991_);
                    v___x_993_ = v_reuseFailAlloc_997_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_994_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_994_, 0, v___x_951_);
                leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
                v___x_995_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_995_, 0, v___x_945_);
                leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
                v_x_932_ = v___x_995_;
                v_x_933_ = v_tail_935_;
                state = 0;
                continue;
            }
            11 => {
                v___x_1003_ = l_Int_repr(v_v_999_);
                leanh::lean_dec(v_v_999_);
                if v_isShared_1002_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1001_, 3);
                    leanh::lean_ctor_set(v___x_1001_, 0, v___x_1003_);
                    v___x_1005_ = v___x_1001_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1009_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1003_);
                    v___x_1005_ = v_reuseFailAlloc_1009_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1006_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1006_, 0, v___x_951_);
                leanh::lean_ctor_set(v___x_1006_, 1, v___x_1005_);
                v___x_1007_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1007_, 0, v___x_945_);
                leanh::lean_ctor_set(v___x_1007_, 1, v___x_1006_);
                v_x_932_ = v___x_1007_;
                v_x_933_ = v_tail_935_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(
    mut v_x_1022_: *mut leanh::LeanObject,
    mut v_x_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v_fst_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_v_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1065_: u8 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_v_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_v_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_v_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_unused_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v_fst_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_v_1139_: u8 = 0;
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v_v_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1177_: u8 = 0;
    let mut v_v_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1190_: u8 = 0;
    let mut v_v_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_unused_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1022_) == 0 {
                    leanh::lean_dec(v_x_1023_);
                    v___x_1024_ = leanh::lean_box(0);
                    return v___x_1024_;
                } else {
                    v_tail_1025_ = leanh::lean_ctor_get(v_x_1022_, 1);
                    if leanh::lean_obj_tag(v_tail_1025_) == 0 {
                        leanh::lean_dec(v_x_1023_);
                        v_head_1026_ = leanh::lean_ctor_get(v_x_1022_, 0);
                        v_isSharedCheck_1109_ = (!leanh::lean_is_exclusive(v_x_1022_)) as u8;
                        if v_isSharedCheck_1109_ == 0 {
                            v_unused_1110_ = leanh::lean_ctor_get(v_x_1022_, 1);
                            leanh::lean_dec(v_unused_1110_);
                            v___x_1028_ = v_x_1022_;
                            v_isShared_1029_ = v_isSharedCheck_1109_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_1026_);
                            leanh::lean_dec(v_x_1022_);
                            v___x_1028_ = leanh::lean_box(0);
                            v_isShared_1029_ = v_isSharedCheck_1109_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_tail_1025_);
                        v_head_1111_ = leanh::lean_ctor_get(v_x_1022_, 0);
                        v_isSharedCheck_1201_ = (!leanh::lean_is_exclusive(v_x_1022_)) as u8;
                        if v_isSharedCheck_1201_ == 0 {
                            v_unused_1202_ = leanh::lean_ctor_get(v_x_1022_, 1);
                            leanh::lean_dec(v_unused_1202_);
                            v___x_1113_ = v_x_1022_;
                            v_isShared_1114_ = v_isSharedCheck_1201_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_1111_);
                            leanh::lean_dec(v_x_1022_);
                            v___x_1113_ = leanh::lean_box(0);
                            v_isShared_1114_ = v_isSharedCheck_1201_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1030_ = leanh::lean_ctor_get(v_head_1026_, 0);
                v_snd_1031_ = leanh::lean_ctor_get(v_head_1026_, 1);
                v_isSharedCheck_1108_ = (!leanh::lean_is_exclusive(v_head_1026_)) as u8;
                if v_isSharedCheck_1108_ == 0 {
                    v___x_1033_ = v_head_1026_;
                    v_isShared_1034_ = v_isSharedCheck_1108_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1031_);
                    leanh::lean_inc(v_fst_1030_);
                    leanh::lean_dec(v_head_1026_);
                    v___x_1033_ = leanh::lean_box(0);
                    v_isShared_1034_ = v_isSharedCheck_1108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1035_ = 1;
                v___x_1036_ = l_Lean_Name_toString(v_fst_1030_, v___x_1035_);
                v___x_1037_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1037_, 0, v___x_1036_);
                v___x_1038_ = l_Lean_instToFormatProdNameDataValue___lam__0___closed__1;
                if v_isShared_1034_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1033_, 5);
                    leanh::lean_ctor_set(v___x_1033_, 1, v___x_1038_);
                    leanh::lean_ctor_set(v___x_1033_, 0, v___x_1037_);
                    v___x_1040_ = v___x_1033_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1038_);
                    v___x_1040_ = v_reuseFailAlloc_1107_;
                    state = 3;
                    continue;
                }
            }
            3 => match leanh::lean_obj_tag(v_snd_1031_) {
                0 => {
                    v_v_1041_ = leanh::lean_ctor_get(v_snd_1031_, 0);
                    v_isSharedCheck_1052_ = (!leanh::lean_is_exclusive(v_snd_1031_)) as u8;
                    if v_isSharedCheck_1052_ == 0 {
                        v___x_1043_ = v_snd_1031_;
                        v_isShared_1044_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1041_);
                        leanh::lean_dec(v_snd_1031_);
                        v___x_1043_ = leanh::lean_box(0);
                        v_isShared_1044_ = v_isSharedCheck_1052_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v_v_1053_ = leanh::lean_ctor_get_uint8(v_snd_1031_, 0 as u32);
                    leanh::lean_dec_ref_known(v_snd_1031_, 0);
                    if v_v_1053_ == 0 {
                        v___x_1054_ = l_Lean_instToFormatDataValue___lam__0___closed__1;
                        if v_isShared_1029_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1028_, 5);
                            leanh::lean_ctor_set(v___x_1028_, 1, v___x_1054_);
                            leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                            v___x_1056_ = v___x_1028_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1057_ =
                                leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1040_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1054_);
                            v___x_1056_ = v_reuseFailAlloc_1057_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_1058_ = l_Lean_instToFormatDataValue___lam__0___closed__3;
                        if v_isShared_1029_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1028_, 5);
                            leanh::lean_ctor_set(v___x_1028_, 1, v___x_1058_);
                            leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                            v___x_1060_ = v___x_1028_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_1061_ =
                                leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1040_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
                            v___x_1060_ = v_reuseFailAlloc_1061_;
                            state = 8;
                            continue;
                        }
                    }
                }
                2 => {
                    v_v_1062_ = leanh::lean_ctor_get(v_snd_1031_, 0);
                    v_isSharedCheck_1075_ = (!leanh::lean_is_exclusive(v_snd_1031_)) as u8;
                    if v_isSharedCheck_1075_ == 0 {
                        v___x_1064_ = v_snd_1031_;
                        v_isShared_1065_ = v_isSharedCheck_1075_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1062_);
                        leanh::lean_dec(v_snd_1031_);
                        v___x_1064_ = leanh::lean_box(0);
                        v_isShared_1065_ = v_isSharedCheck_1075_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v_v_1076_ = leanh::lean_ctor_get(v_snd_1031_, 0);
                    v_isSharedCheck_1087_ = (!leanh::lean_is_exclusive(v_snd_1031_)) as u8;
                    if v_isSharedCheck_1087_ == 0 {
                        v___x_1078_ = v_snd_1031_;
                        v_isShared_1079_ = v_isSharedCheck_1087_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1076_);
                        leanh::lean_dec(v_snd_1031_);
                        v___x_1078_ = leanh::lean_box(0);
                        v_isShared_1079_ = v_isSharedCheck_1087_;
                        state = 12;
                        continue;
                    }
                }
                4 => {
                    v_v_1088_ = leanh::lean_ctor_get(v_snd_1031_, 0);
                    v_isSharedCheck_1099_ = (!leanh::lean_is_exclusive(v_snd_1031_)) as u8;
                    if v_isSharedCheck_1099_ == 0 {
                        v___x_1090_ = v_snd_1031_;
                        v_isShared_1091_ = v_isSharedCheck_1099_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1088_);
                        leanh::lean_dec(v_snd_1031_);
                        v___x_1090_ = leanh::lean_box(0);
                        v_isShared_1091_ = v_isSharedCheck_1099_;
                        state = 15;
                        continue;
                    }
                }
                _ => {
                    v_v_1100_ = leanh::lean_ctor_get(v_snd_1031_, 0);
                    leanh::lean_inc(v_v_1100_);
                    leanh::lean_dec_ref_known(v_snd_1031_, 1);
                    v___x_1101_ = leanh::lean_box(0);
                    v___x_1102_ = 0;
                    v___x_1103_ = l_Lean_Syntax_formatStx(v_v_1100_, v___x_1101_, v___x_1102_);
                    if v_isShared_1029_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1028_, 5);
                        leanh::lean_ctor_set(v___x_1028_, 1, v___x_1103_);
                        leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                        v___x_1105_ = v___x_1028_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1040_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
                        v___x_1105_ = v_reuseFailAlloc_1106_;
                        state = 18;
                        continue;
                    }
                }
            },
            4 => {
                v___x_1045_ = l_String_quote(v_v_1041_);
                if v_isShared_1044_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1043_, 3);
                    leanh::lean_ctor_set(v___x_1043_, 0, v___x_1045_);
                    v___x_1047_ = v___x_1043_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1051_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1045_);
                    v___x_1047_ = v_reuseFailAlloc_1051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1029_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1028_, 5);
                    leanh::lean_ctor_set(v___x_1028_, 1, v___x_1047_);
                    leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                    v___x_1049_ = v___x_1028_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1047_);
                    v___x_1049_ = v_reuseFailAlloc_1050_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1049_;
            }
            7 => {
                return v___x_1056_;
            }
            8 => {
                return v___x_1060_;
            }
            9 => {
                v___x_1066_ = l_Lean_instToFormatDataValue___lam__0___closed__5;
                v___x_1067_ = l_Lean_Name_toString(v_v_1062_, v___x_1035_);
                if v_isShared_1065_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1064_, 3);
                    leanh::lean_ctor_set(v___x_1064_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1064_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1074_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1029_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1028_, 5);
                    leanh::lean_ctor_set(v___x_1028_, 1, v___x_1069_);
                    leanh::lean_ctor_set(v___x_1028_, 0, v___x_1066_);
                    v___x_1071_ = v___x_1028_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1073_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1073_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1072_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1072_, 0, v___x_1040_);
                leanh::lean_ctor_set(v___x_1072_, 1, v___x_1071_);
                return v___x_1072_;
            }
            12 => {
                v___x_1080_ = l_Nat_reprFast(v_v_1076_);
                if v_isShared_1079_ == 0 {
                    leanh::lean_ctor_set(v___x_1078_, 0, v___x_1080_);
                    v___x_1082_ = v___x_1078_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1080_);
                    v___x_1082_ = v_reuseFailAlloc_1086_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1029_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1028_, 5);
                    leanh::lean_ctor_set(v___x_1028_, 1, v___x_1082_);
                    leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                    v___x_1084_ = v___x_1028_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1084_;
            }
            15 => {
                v___x_1092_ = l_Int_repr(v_v_1088_);
                leanh::lean_dec(v_v_1088_);
                if v_isShared_1091_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1090_, 3);
                    leanh::lean_ctor_set(v___x_1090_, 0, v___x_1092_);
                    v___x_1094_ = v___x_1090_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1092_);
                    v___x_1094_ = v_reuseFailAlloc_1098_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1029_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1028_, 5);
                    leanh::lean_ctor_set(v___x_1028_, 1, v___x_1094_);
                    leanh::lean_ctor_set(v___x_1028_, 0, v___x_1040_);
                    v___x_1096_ = v___x_1028_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1096_;
            }
            18 => {
                return v___x_1105_;
            }
            19 => {
                v_fst_1115_ = leanh::lean_ctor_get(v_head_1111_, 0);
                v_snd_1116_ = leanh::lean_ctor_get(v_head_1111_, 1);
                v_isSharedCheck_1200_ = (!leanh::lean_is_exclusive(v_head_1111_)) as u8;
                if v_isSharedCheck_1200_ == 0 {
                    v___x_1118_ = v_head_1111_;
                    v_isShared_1119_ = v_isSharedCheck_1200_;
                    state = 20;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1116_);
                    leanh::lean_inc(v_fst_1115_);
                    leanh::lean_dec(v_head_1111_);
                    v___x_1118_ = leanh::lean_box(0);
                    v_isShared_1119_ = v_isSharedCheck_1200_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_1120_ = 1;
                v___x_1121_ = l_Lean_Name_toString(v_fst_1115_, v___x_1120_);
                v___x_1122_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                v___x_1123_ = l_Lean_instToFormatProdNameDataValue___lam__0___closed__1;
                if v_isShared_1119_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1118_, 5);
                    leanh::lean_ctor_set(v___x_1118_, 1, v___x_1123_);
                    leanh::lean_ctor_set(v___x_1118_, 0, v___x_1122_);
                    v___x_1125_ = v___x_1118_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1122_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1123_);
                    v___x_1125_ = v_reuseFailAlloc_1199_;
                    state = 21;
                    continue;
                }
            }
            21 => match leanh::lean_obj_tag(v_snd_1116_) {
                0 => {
                    v_v_1126_ = leanh::lean_ctor_get(v_snd_1116_, 0);
                    v_isSharedCheck_1138_ = (!leanh::lean_is_exclusive(v_snd_1116_)) as u8;
                    if v_isSharedCheck_1138_ == 0 {
                        v___x_1128_ = v_snd_1116_;
                        v_isShared_1129_ = v_isSharedCheck_1138_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1126_);
                        leanh::lean_dec(v_snd_1116_);
                        v___x_1128_ = leanh::lean_box(0);
                        v_isShared_1129_ = v_isSharedCheck_1138_;
                        state = 22;
                        continue;
                    }
                }
                1 => {
                    v_v_1139_ = leanh::lean_ctor_get_uint8(v_snd_1116_, 0 as u32);
                    leanh::lean_dec_ref_known(v_snd_1116_, 0);
                    if v_v_1139_ == 0 {
                        v___x_1140_ = l_Lean_instToFormatDataValue___lam__0___closed__1;
                        if v_isShared_1114_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1113_, 5);
                            leanh::lean_ctor_set(v___x_1113_, 1, v___x_1140_);
                            leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                            v___x_1142_ = v___x_1113_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_1144_ =
                                leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1125_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1140_);
                            v___x_1142_ = v_reuseFailAlloc_1144_;
                            state = 25;
                            continue;
                        }
                    } else {
                        v___x_1145_ = l_Lean_instToFormatDataValue___lam__0___closed__3;
                        if v_isShared_1114_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1113_, 5);
                            leanh::lean_ctor_set(v___x_1113_, 1, v___x_1145_);
                            leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                            v___x_1147_ = v___x_1113_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_1149_ =
                                leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1125_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1145_);
                            v___x_1147_ = v_reuseFailAlloc_1149_;
                            state = 26;
                            continue;
                        }
                    }
                }
                2 => {
                    v_v_1150_ = leanh::lean_ctor_get(v_snd_1116_, 0);
                    v_isSharedCheck_1164_ = (!leanh::lean_is_exclusive(v_snd_1116_)) as u8;
                    if v_isSharedCheck_1164_ == 0 {
                        v___x_1152_ = v_snd_1116_;
                        v_isShared_1153_ = v_isSharedCheck_1164_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1150_);
                        leanh::lean_dec(v_snd_1116_);
                        v___x_1152_ = leanh::lean_box(0);
                        v_isShared_1153_ = v_isSharedCheck_1164_;
                        state = 27;
                        continue;
                    }
                }
                3 => {
                    v_v_1165_ = leanh::lean_ctor_get(v_snd_1116_, 0);
                    v_isSharedCheck_1177_ = (!leanh::lean_is_exclusive(v_snd_1116_)) as u8;
                    if v_isSharedCheck_1177_ == 0 {
                        v___x_1167_ = v_snd_1116_;
                        v_isShared_1168_ = v_isSharedCheck_1177_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1165_);
                        leanh::lean_dec(v_snd_1116_);
                        v___x_1167_ = leanh::lean_box(0);
                        v_isShared_1168_ = v_isSharedCheck_1177_;
                        state = 30;
                        continue;
                    }
                }
                4 => {
                    v_v_1178_ = leanh::lean_ctor_get(v_snd_1116_, 0);
                    v_isSharedCheck_1190_ = (!leanh::lean_is_exclusive(v_snd_1116_)) as u8;
                    if v_isSharedCheck_1190_ == 0 {
                        v___x_1180_ = v_snd_1116_;
                        v_isShared_1181_ = v_isSharedCheck_1190_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1178_);
                        leanh::lean_dec(v_snd_1116_);
                        v___x_1180_ = leanh::lean_box(0);
                        v_isShared_1181_ = v_isSharedCheck_1190_;
                        state = 33;
                        continue;
                    }
                }
                _ => {
                    v_v_1191_ = leanh::lean_ctor_get(v_snd_1116_, 0);
                    leanh::lean_inc(v_v_1191_);
                    leanh::lean_dec_ref_known(v_snd_1116_, 1);
                    v___x_1192_ = leanh::lean_box(0);
                    v___x_1193_ = 0;
                    v___x_1194_ = l_Lean_Syntax_formatStx(v_v_1191_, v___x_1192_, v___x_1193_);
                    if v_isShared_1114_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1113_, 5);
                        leanh::lean_ctor_set(v___x_1113_, 1, v___x_1194_);
                        leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                        v___x_1196_ = v___x_1113_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_1198_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1125_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1194_);
                        v___x_1196_ = v_reuseFailAlloc_1198_;
                        state = 36;
                        continue;
                    }
                }
            },
            22 => {
                v___x_1130_ = l_String_quote(v_v_1126_);
                if v_isShared_1129_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1128_, 3);
                    leanh::lean_ctor_set(v___x_1128_, 0, v___x_1130_);
                    v___x_1132_ = v___x_1128_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1130_);
                    v___x_1132_ = v_reuseFailAlloc_1137_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1114_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1113_, 5);
                    leanh::lean_ctor_set(v___x_1113_, 1, v___x_1132_);
                    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                    v___x_1134_ = v___x_1113_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1132_);
                    v___x_1134_ = v_reuseFailAlloc_1136_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_1135_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1134_, v_tail_1025_);
                return v___x_1135_;
            }
            25 => {
                v___x_1143_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1142_, v_tail_1025_);
                return v___x_1143_;
            }
            26 => {
                v___x_1148_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1147_, v_tail_1025_);
                return v___x_1148_;
            }
            27 => {
                v___x_1154_ = l_Lean_instToFormatDataValue___lam__0___closed__5;
                v___x_1155_ = l_Lean_Name_toString(v_v_1150_, v___x_1120_);
                if v_isShared_1153_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1152_, 3);
                    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1152_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1163_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1155_);
                    v___x_1157_ = v_reuseFailAlloc_1163_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1114_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1113_, 5);
                    leanh::lean_ctor_set(v___x_1113_, 1, v___x_1157_);
                    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1154_);
                    v___x_1159_ = v___x_1113_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1157_);
                    v___x_1159_ = v_reuseFailAlloc_1162_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_1160_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1160_, 0, v___x_1125_);
                leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                v___x_1161_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1160_, v_tail_1025_);
                return v___x_1161_;
            }
            30 => {
                v___x_1169_ = l_Nat_reprFast(v_v_1165_);
                if v_isShared_1168_ == 0 {
                    leanh::lean_ctor_set(v___x_1167_, 0, v___x_1169_);
                    v___x_1171_ = v___x_1167_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1176_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1169_);
                    v___x_1171_ = v_reuseFailAlloc_1176_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_1114_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1113_, 5);
                    leanh::lean_ctor_set(v___x_1113_, 1, v___x_1171_);
                    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                    v___x_1173_ = v___x_1113_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1171_);
                    v___x_1173_ = v_reuseFailAlloc_1175_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_1174_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1173_, v_tail_1025_);
                return v___x_1174_;
            }
            33 => {
                v___x_1182_ = l_Int_repr(v_v_1178_);
                leanh::lean_dec(v_v_1178_);
                if v_isShared_1181_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1180_, 3);
                    leanh::lean_ctor_set(v___x_1180_, 0, v___x_1182_);
                    v___x_1184_ = v___x_1180_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1189_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1182_);
                    v___x_1184_ = v_reuseFailAlloc_1189_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_1114_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1113_, 5);
                    leanh::lean_ctor_set(v___x_1113_, 1, v___x_1184_);
                    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1125_);
                    v___x_1186_ = v___x_1113_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1184_);
                    v___x_1186_ = v_reuseFailAlloc_1188_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1187_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1186_, v_tail_1025_);
                return v___x_1187_;
            }
            36 => {
                v___x_1197_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_1023_, v___x_1196_, v_tail_1025_);
                return v___x_1197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_formatKVMap___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_formatKVMap___closed__2;
    v___x_1209_ = lean_string_length(v___x_1208_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_formatKVMap___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_formatKVMap___closed__4),
        core::ptr::addr_of_mut!(l_Lean_formatKVMap___closed__4_once),
        _init_l_Lean_formatKVMap___closed__4,
    );
    v___x_1211_ = lean_nat_to_int(v___x_1210_);
    return v___x_1211_;
}
pub unsafe fn l_Lean_formatKVMap(
    mut v_m_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = l_Lean_formatKVMap___closed__1;
    v___x_1218_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_1216_, v___x_1217_);
    v___x_1219_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_formatKVMap___closed__5),
        core::ptr::addr_of_mut!(l_Lean_formatKVMap___closed__5_once),
        _init_l_Lean_formatKVMap___closed__5,
    );
    v___x_1220_ = l_Lean_formatKVMap___closed__6;
    v___x_1221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1221_, 0, v___x_1220_);
    leanh::lean_ctor_set(v___x_1221_, 1, v___x_1218_);
    v___x_1222_ = l_Lean_formatKVMap___closed__7;
    v___x_1223_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1223_, 0, v___x_1221_);
    leanh::lean_ctor_set(v___x_1223_, 1, v___x_1222_);
    v___x_1224_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1224_, 0, v___x_1219_);
    leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    v___x_1225_ = 0;
    v___x_1226_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1224_);
    leanh::lean_ctor_set_uint8(
        v___x_1226_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1225_,
    );
    return v___x_1226_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Std_Format_format_width = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Std_Format_format_width);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Std_Format_format_unicode = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Std_Format_format_unicode);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Std_Format_format_indent = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Std_Format_format_indent);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Format(builtin);
}