// Lean compiler output
// Module: Lean.Elab.Tactic.Rfl
// Imports: Lean.Meta.Tactic.Rfl
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::Rfl::{
    initialize_Lean_Meta_Tactic_Rfl, l_Lean_MVarId_applyRfl,
    runtime_initialize_Lean_Meta_Tactic_Rfl,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value: LeanStringObject<9> =
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
        m_data: [97, 112, 112, 108, 121, 82, 102, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value)
                as *mut LeanObject,
            18128203598290488495 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 65, 112, 112, 108, 121, 82, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value) as *mut LeanObject,9736486422574606045 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value) as *mut LeanObject,16816156489251953870 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0_value: LeanStringObject<183> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 183, m_capacity: 183, m_length: 182, m_data: [84, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 97, 32, 103, 111, 97, 108, 32, 119, 104, 111, 115, 101, 32, 116, 97, 114, 103, 101, 116, 32, 104, 97, 115, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 120, 32, 126, 32, 120, 96, 44, 32, 119, 104, 101, 114, 101, 32, 96, 126, 96, 32, 105, 115, 32, 97, 32, 114, 101, 102, 108, 101, 120, 105, 118, 101, 10, 114, 101, 108, 97, 116, 105, 111, 110, 44, 32, 116, 104, 97, 116, 32, 105, 115, 44, 32, 97, 32, 114, 101, 108, 97, 116, 105, 111, 110, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 97, 32, 114, 101, 102, 108, 101, 120, 105, 118, 101, 32, 108, 101, 109, 109, 97, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 91, 114, 101, 102, 108, 93, 46, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut LeanObject,((( 62 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value) as *mut LeanObject,((( 62 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    v___x_187_ = lean_box(0);
    v___x_188_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_189_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_189_, 0, v___x_188_);
    lean_ctor_set(v___x_189_, 1, v___x_187_);
    return v___x_189_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_191_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0);
    v___x_192_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_192_, 0, v___x_191_);
    return v___x_192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___boxed(
    mut v___y_193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_194_: *mut LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
    return v_res_194_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0(
    mut v_00_u03b1_195_: *mut LeanObject,
    mut v___y_196_: *mut LeanObject,
    mut v___y_197_: *mut LeanObject,
    mut v___y_198_: *mut LeanObject,
    mut v___y_199_: *mut LeanObject,
    mut v___y_200_: *mut LeanObject,
    mut v___y_201_: *mut LeanObject,
    mut v___y_202_: *mut LeanObject,
    mut v___y_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
    return v___x_205_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___boxed(
    mut v_00_u03b1_206_: *mut LeanObject,
    mut v___y_207_: *mut LeanObject,
    mut v___y_208_: *mut LeanObject,
    mut v___y_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v___y_213_: *mut LeanObject,
    mut v___y_214_: *mut LeanObject,
    mut v___y_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0(
            v_00_u03b1_206_,
            v___y_207_,
            v___y_208_,
            v___y_209_,
            v___y_210_,
            v___y_211_,
            v___y_212_,
            v___y_213_,
            v___y_214_,
        );
    lean_dec(v___y_214_);
    lean_dec_ref(v___y_213_);
    lean_dec(v___y_212_);
    lean_dec_ref(v___y_211_);
    lean_dec(v___y_210_);
    lean_dec_ref(v___y_209_);
    lean_dec(v___y_208_);
    lean_dec_ref(v___y_207_);
    return v_res_216_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0(
    mut v___y_217_: *mut LeanObject,
    mut v___y_218_: *mut LeanObject,
    mut v___y_219_: *mut LeanObject,
    mut v___y_220_: *mut LeanObject,
    mut v___y_221_: *mut LeanObject,
    mut v___y_222_: *mut LeanObject,
    mut v___y_223_: *mut LeanObject,
    mut v___y_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_238_: u8 = 0;
    let mut v_unused_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_226_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                );
                if lean_obj_tag(v___x_226_) == 0 {
                    v_a_227_ = lean_ctor_get(v___x_226_, 0);
                    lean_inc(v_a_227_);
                    lean_dec_ref_known(v___x_226_, 1);
                    v___x_228_ = l_Lean_MVarId_applyRfl(
                        v_a_227_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                    );
                    if lean_obj_tag(v___x_228_) == 0 {
                        lean_dec_ref_known(v___x_228_, 1);
                        v___x_229_ = lean_box(0);
                        v___x_230_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_229_, v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                        );
                        if lean_obj_tag(v___x_230_) == 0 {
                            v_isSharedCheck_238_ = (!lean_is_exclusive(v___x_230_)) as u8;
                            if v_isSharedCheck_238_ == 0 {
                                v_unused_239_ = lean_ctor_get(v___x_230_, 0);
                                lean_dec(v_unused_239_);
                                v___x_232_ = v___x_230_;
                                v_isShared_233_ = v_isSharedCheck_238_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_230_);
                                v___x_232_ = lean_box(0);
                                v_isShared_233_ = v_isSharedCheck_238_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_230_;
                        }
                    } else {
                        return v___x_228_;
                    }
                } else {
                    v_a_240_ = lean_ctor_get(v___x_226_, 0);
                    v_isSharedCheck_247_ = (!lean_is_exclusive(v___x_226_)) as u8;
                    if v_isSharedCheck_247_ == 0 {
                        v___x_242_ = v___x_226_;
                        v_isShared_243_ = v_isSharedCheck_247_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_240_);
                        lean_dec(v___x_226_);
                        v___x_242_ = lean_box(0);
                        v_isShared_243_ = v_isSharedCheck_247_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_234_ = lean_box(0);
                if v_isShared_233_ == 0 {
                    lean_ctor_set(v___x_232_, 0, v___x_234_);
                    v___x_236_ = v___x_232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
                    v___x_236_ = v_reuseFailAlloc_237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_236_;
            }
            3 => {
                if v_isShared_243_ == 0 {
                    v___x_245_ = v___x_242_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
                    v___x_245_ = v_reuseFailAlloc_246_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0___boxed(
    mut v___y_248_: *mut LeanObject,
    mut v___y_249_: *mut LeanObject,
    mut v___y_250_: *mut LeanObject,
    mut v___y_251_: *mut LeanObject,
    mut v___y_252_: *mut LeanObject,
    mut v___y_253_: *mut LeanObject,
    mut v___y_254_: *mut LeanObject,
    mut v___y_255_: *mut LeanObject,
    mut v___y_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_257_: *mut LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0(
        v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_,
        v___y_255_,
    );
    lean_dec(v___y_255_);
    lean_dec_ref(v___y_254_);
    lean_dec(v___y_253_);
    lean_dec_ref(v___y_252_);
    lean_dec(v___y_251_);
    lean_dec_ref(v___y_250_);
    lean_dec(v___y_249_);
    lean_dec_ref(v___y_248_);
    return v_res_257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1(
    mut v___f_258_: *mut LeanObject,
    mut v___y_259_: *mut LeanObject,
    mut v___y_260_: *mut LeanObject,
    mut v___y_261_: *mut LeanObject,
    mut v___y_262_: *mut LeanObject,
    mut v___y_263_: *mut LeanObject,
    mut v___y_264_: *mut LeanObject,
    mut v___y_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_,
        v___y_265_, v___y_266_,
    );
    return v___x_268_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1___boxed(
    mut v___f_269_: *mut LeanObject,
    mut v___y_270_: *mut LeanObject,
    mut v___y_271_: *mut LeanObject,
    mut v___y_272_: *mut LeanObject,
    mut v___y_273_: *mut LeanObject,
    mut v___y_274_: *mut LeanObject,
    mut v___y_275_: *mut LeanObject,
    mut v___y_276_: *mut LeanObject,
    mut v___y_277_: *mut LeanObject,
    mut v___y_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_279_: *mut LeanObject = core::ptr::null_mut();
    v_res_279_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1(
        v___f_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_,
        v___y_276_, v___y_277_,
    );
    lean_dec(v___y_277_);
    lean_dec_ref(v___y_276_);
    lean_dec(v___y_275_);
    lean_dec_ref(v___y_274_);
    lean_dec(v___y_273_);
    lean_dec_ref(v___y_272_);
    lean_dec(v___y_271_);
    lean_dec_ref(v___y_270_);
    return v_res_279_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl(
    mut v_stx_292_: *mut LeanObject,
    mut v_a_293_: *mut LeanObject,
    mut v_a_294_: *mut LeanObject,
    mut v_a_295_: *mut LeanObject,
    mut v_a_296_: *mut LeanObject,
    mut v_a_297_: *mut LeanObject,
    mut v_a_298_: *mut LeanObject,
    mut v_a_299_: *mut LeanObject,
    mut v_a_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: u8 = 0;
    v___x_302_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4;
    v___x_303_ = l_Lean_Syntax_isOfKind(v_stx_292_, v___x_302_);
    if v___x_303_ == 0 {
        let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
        v___x_304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
        return v___x_304_;
    } else {
        let mut v___f_305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        v___f_305_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6;
        v___x_306_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_305_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_,
            v_a_300_,
        );
        return v___x_306_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___boxed(
    mut v_stx_307_: *mut LeanObject,
    mut v_a_308_: *mut LeanObject,
    mut v_a_309_: *mut LeanObject,
    mut v_a_310_: *mut LeanObject,
    mut v_a_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
    mut v_a_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_a_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_317_: *mut LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl(
        v_stx_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_,
    );
    lean_dec(v_a_315_);
    lean_dec_ref(v_a_314_);
    lean_dec(v_a_313_);
    lean_dec_ref(v_a_312_);
    lean_dec(v_a_311_);
    lean_dec_ref(v_a_310_);
    lean_dec(v_a_309_);
    lean_dec_ref(v_a_308_);
    return v_res_317_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1()
-> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_329_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4;
    v___x_330_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_331_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Rfl_evalApplyRfl___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_332_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_328_, v___x_329_, v___x_330_, v___x_331_,
    );
    return v___x_332_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___boxed(
    mut v_a_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1();
    return v_res_334_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3()
-> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_338_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0;
    v___x_339_ = l_Lean_addBuiltinDocString(v___x_337_, v___x_338_);
    return v___x_339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___boxed(
    mut v_a_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_341_: *mut LeanObject = core::ptr::null_mut();
    v_res_341_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3();
    return v_res_341_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5()
-> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_369_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6;
    v___x_370_ = l_Lean_addBuiltinDeclarationRanges(v___x_368_, v___x_369_);
    return v___x_370_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___boxed(
    mut v_a_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_372_: *mut LeanObject = core::ptr::null_mut();
    v_res_372_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5();
    return v_res_372_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Rfl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Rfl(builtin);
}
