// Lean compiler output
// Module: Lean.Elab.Tactic.Congr
// Imports: Lean.Meta.Tactic.Congr Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getNat};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr7, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::Congr::{
    initialize_Lean_Meta_Tactic_Congr, l_Lean_MVarId_congrN,
    runtime_initialize_Lean_Meta_Tactic_Congr,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value: LeanStringObject<6> =
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
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value)
                as *mut LeanObject,
            7757010358911522857 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 67, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value) as *mut LeanObject,8091555762121448132 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut LeanObject,8241698261642232286 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value) as *mut LeanObject,15114071845524100611 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value) as *mut LeanObject,4478290776814184064 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = lean_box(0);
    v___x_187_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_188_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_188_, 0, v___x_187_);
    lean_ctor_set(v___x_188_, 1, v___x_186_);
    return v___x_188_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    v___x_190_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0);
    v___x_191_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_191_, 0, v___x_190_);
    return v___x_191_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___boxed(
    mut v___y_192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_193_: *mut LeanObject = core::ptr::null_mut();
    v_res_193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
    return v_res_193_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(
    mut v_00_u03b1_194_: *mut LeanObject,
    mut v___y_195_: *mut LeanObject,
    mut v___y_196_: *mut LeanObject,
    mut v___y_197_: *mut LeanObject,
    mut v___y_198_: *mut LeanObject,
    mut v___y_199_: *mut LeanObject,
    mut v___y_200_: *mut LeanObject,
    mut v___y_201_: *mut LeanObject,
    mut v___y_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    v___x_204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
    return v___x_204_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___boxed(
    mut v_00_u03b1_205_: *mut LeanObject,
    mut v___y_206_: *mut LeanObject,
    mut v___y_207_: *mut LeanObject,
    mut v___y_208_: *mut LeanObject,
    mut v___y_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v___y_213_: *mut LeanObject,
    mut v___y_214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_215_: *mut LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(v_00_u03b1_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
    lean_dec(v___y_213_);
    lean_dec_ref(v___y_212_);
    lean_dec(v___y_211_);
    lean_dec_ref(v___y_210_);
    lean_dec(v___y_209_);
    lean_dec_ref(v___y_208_);
    lean_dec(v___y_207_);
    lean_dec_ref(v___y_206_);
    return v_res_215_;
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(
    mut v___y_216_: *mut LeanObject,
    mut v___x_217_: u8,
    mut v___y_218_: *mut LeanObject,
    mut v___y_219_: *mut LeanObject,
    mut v___y_220_: *mut LeanObject,
    mut v___y_221_: *mut LeanObject,
    mut v___y_222_: *mut LeanObject,
    mut v___y_223_: *mut LeanObject,
    mut v___y_224_: *mut LeanObject,
    mut v___y_225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_234_: u8 = 0;
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_239_: u8 = 0;
    let mut v_unused_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_248_: u8 = 0;
    let mut v_a_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_252_: u8 = 0;
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_227_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_219_, v___y_222_, v___y_223_, v___y_224_, v___y_225_,
                );
                if lean_obj_tag(v___x_227_) == 0 {
                    v_a_228_ = lean_ctor_get(v___x_227_, 0);
                    lean_inc(v_a_228_);
                    lean_dec_ref_known(v___x_227_, 1);
                    v___x_229_ = l_Lean_MVarId_congrN(
                        v_a_228_, v___y_216_, v___x_217_, v___x_217_, v___y_222_, v___y_223_,
                        v___y_224_, v___y_225_,
                    );
                    if lean_obj_tag(v___x_229_) == 0 {
                        v_a_230_ = lean_ctor_get(v___x_229_, 0);
                        lean_inc(v_a_230_);
                        lean_dec_ref_known(v___x_229_, 1);
                        v___x_231_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v_a_230_, v___y_219_, v___y_222_, v___y_223_, v___y_224_, v___y_225_,
                        );
                        if lean_obj_tag(v___x_231_) == 0 {
                            v_isSharedCheck_239_ = (!lean_is_exclusive(v___x_231_)) as u8;
                            if v_isSharedCheck_239_ == 0 {
                                v_unused_240_ = lean_ctor_get(v___x_231_, 0);
                                lean_dec(v_unused_240_);
                                v___x_233_ = v___x_231_;
                                v_isShared_234_ = v_isSharedCheck_239_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_231_);
                                v___x_233_ = lean_box(0);
                                v_isShared_234_ = v_isSharedCheck_239_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_231_;
                        }
                    } else {
                        v_a_241_ = lean_ctor_get(v___x_229_, 0);
                        v_isSharedCheck_248_ = (!lean_is_exclusive(v___x_229_)) as u8;
                        if v_isSharedCheck_248_ == 0 {
                            v___x_243_ = v___x_229_;
                            v_isShared_244_ = v_isSharedCheck_248_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_241_);
                            lean_dec(v___x_229_);
                            v___x_243_ = lean_box(0);
                            v_isShared_244_ = v_isSharedCheck_248_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_249_ = lean_ctor_get(v___x_227_, 0);
                    v_isSharedCheck_256_ = (!lean_is_exclusive(v___x_227_)) as u8;
                    if v_isSharedCheck_256_ == 0 {
                        v___x_251_ = v___x_227_;
                        v_isShared_252_ = v_isSharedCheck_256_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_249_);
                        lean_dec(v___x_227_);
                        v___x_251_ = lean_box(0);
                        v_isShared_252_ = v_isSharedCheck_256_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_235_ = lean_box(0);
                if v_isShared_234_ == 0 {
                    lean_ctor_set(v___x_233_, 0, v___x_235_);
                    v___x_237_ = v___x_233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
                    v___x_237_ = v_reuseFailAlloc_238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_237_;
            }
            3 => {
                if v_isShared_244_ == 0 {
                    v___x_246_ = v___x_243_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
                    v___x_246_ = v_reuseFailAlloc_247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_246_;
            }
            5 => {
                if v_isShared_252_ == 0 {
                    v___x_254_ = v___x_251_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
                    v___x_254_ = v_reuseFailAlloc_255_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed(
    mut v___y_257_: *mut LeanObject,
    mut v___x_258_: *mut LeanObject,
    mut v___y_259_: *mut LeanObject,
    mut v___y_260_: *mut LeanObject,
    mut v___y_261_: *mut LeanObject,
    mut v___y_262_: *mut LeanObject,
    mut v___y_263_: *mut LeanObject,
    mut v___y_264_: *mut LeanObject,
    mut v___y_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
    mut v___y_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_876__boxed_268_: u8 = 0;
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v___x_876__boxed_268_ = (lean_unbox(v___x_258_) as u8);
    v_res_269_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(
        v___y_257_,
        v___x_876__boxed_268_,
        v___y_259_,
        v___y_260_,
        v___y_261_,
        v___y_262_,
        v___y_263_,
        v___y_264_,
        v___y_265_,
        v___y_266_,
    );
    lean_dec(v___y_266_);
    lean_dec_ref(v___y_265_);
    lean_dec(v___y_264_);
    lean_dec_ref(v___y_263_);
    lean_dec(v___y_262_);
    lean_dec_ref(v___y_261_);
    lean_dec(v___y_260_);
    lean_dec_ref(v___y_259_);
    lean_dec(v___y_257_);
    return v_res_269_;
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(
    mut v_stx_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_a_284_: *mut LeanObject,
    mut v_a_285_: *mut LeanObject,
    mut v_a_286_: *mut LeanObject,
    mut v_a_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    let mut v___y_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: u8 = 0;
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_x3f_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hugeDepth_313_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_289_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4;
                lean_inc(v_stx_279_);
                v___x_290_ = l_Lean_Syntax_isOfKind(v_stx_279_, v___x_289_);
                if v___x_290_ == 0 {
                    lean_dec(v_stx_279_);
                    v___x_304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
                    return v___x_304_;
                } else {
                    v___x_305_ = lean_unsigned_to_nat(1);
                    v___x_306_ = l_Lean_Syntax_getArg(v_stx_279_, v___x_305_);
                    lean_dec(v_stx_279_);
                    v___x_307_ = l_Lean_Syntax_isNone(v___x_306_);
                    if v___x_307_ == 0 {
                        lean_inc(v___x_306_);
                        v___x_308_ = l_Lean_Syntax_matchesNull(v___x_306_, v___x_305_);
                        if v___x_308_ == 0 {
                            lean_dec(v___x_306_);
                            v___x_309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
                            return v___x_309_;
                        } else {
                            v___x_310_ = lean_unsigned_to_nat(0);
                            v_n_x3f_311_ = l_Lean_Syntax_getArg(v___x_306_, v___x_310_);
                            lean_dec(v___x_306_);
                            v___x_312_ = l_Lean_TSyntax_getNat(v_n_x3f_311_);
                            lean_dec(v_n_x3f_311_);
                            v___y_292_ = v_a_281_;
                            v___y_293_ = v_a_286_;
                            v___y_294_ = v_a_285_;
                            v___y_295_ = v_a_284_;
                            v___y_296_ = v_a_287_;
                            v___y_297_ = v_a_282_;
                            v___y_298_ = v_a_280_;
                            v___y_299_ = v_a_283_;
                            v___y_300_ = v___x_312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_306_);
                        v_hugeDepth_313_ = lean_unsigned_to_nat(1000000);
                        v___y_292_ = v_a_281_;
                        v___y_293_ = v_a_286_;
                        v___y_294_ = v_a_285_;
                        v___y_295_ = v_a_284_;
                        v___y_296_ = v_a_287_;
                        v___y_297_ = v_a_282_;
                        v___y_298_ = v_a_280_;
                        v___y_299_ = v_a_283_;
                        v___y_300_ = v_hugeDepth_313_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_301_ = lean_box((v___x_290_) as usize);
                v___f_302_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    2,
                );
                lean_closure_set(v___f_302_, 0, v___y_300_);
                lean_closure_set(v___f_302_, 1, v___x_301_);
                v___x_303_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_302_, v___y_298_, v___y_292_, v___y_297_, v___y_299_, v___y_295_,
                    v___y_294_, v___y_293_, v___y_296_,
                );
                return v___x_303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed(
    mut v_stx_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_a_316_: *mut LeanObject,
    mut v_a_317_: *mut LeanObject,
    mut v_a_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
    mut v_a_322_: *mut LeanObject,
    mut v_a_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_324_: *mut LeanObject = core::ptr::null_mut();
    v_res_324_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(
        v_stx_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_,
    );
    lean_dec(v_a_322_);
    lean_dec_ref(v_a_321_);
    lean_dec(v_a_320_);
    lean_dec_ref(v_a_319_);
    lean_dec(v_a_318_);
    lean_dec_ref(v_a_317_);
    lean_dec(v_a_316_);
    lean_dec_ref(v_a_315_);
    return v_res_324_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1()
-> *mut LeanObject {
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_334_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4;
    v___x_335_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2;
    v___x_336_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_337_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_333_, v___x_334_, v___x_335_, v___x_336_,
    );
    return v___x_337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___boxed(
    mut v_a_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
    return v_res_339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3()
-> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2;
    v___x_367_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6;
    v___x_368_ = l_Lean_addBuiltinDeclarationRanges(v___x_366_, v___x_367_);
    return v___x_368_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___boxed(
    mut v_a_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_370_: *mut LeanObject = core::ptr::null_mut();
    v_res_370_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
    return v_res_370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Congr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Congr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Congr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Congr(builtin);
}
