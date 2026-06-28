// Lean compiler output
// Module: Lean.Elab.Tactic.Symm
// Imports: Lean.Meta.Tactic.Symm Lean.Elab.Tactic.Location
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Tactic::Symm::{
    initialize_Lean_Meta_Tactic_Symm, l_Lean_MVarId_applySymm, l_Lean_MVarId_applySymmAt,
    l_Lean_MVarId_symmSaturate, runtime_initialize_Lean_Meta_Tactic_Symm,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
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
            96, 115, 121, 109, 109, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111,
            103, 114, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalSymm___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_evalSymm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_evalSymm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_evalSymm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__3_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 121, 109, 109, 0],
};
static mut l_Lean_Elab_Tactic_evalSymm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalSymm___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__3_value) as *mut LeanObject,
        7650210744778290473 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalSymm___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalSymm___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSymm___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__6_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Elab_Tactic_evalSymm___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__5_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSymm___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalSymm___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSymm___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalSymm___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSymm___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymm___closed__9_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_evalSymm___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 83, 121, 109, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value) as *mut LeanObject,15361828905738109939 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [115, 121, 109, 109, 83, 97, 116, 117, 114, 97, 116, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalSymmSaturate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value)
                as *mut LeanObject,
            13734569320710453810 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSymmSaturate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSymmSaturate___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalSymmSaturate___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSymmSaturate___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymmSaturate___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 83, 121, 109, 109, 83, 97, 116, 117, 114, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSymm___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value) as *mut LeanObject,12253806134294488731 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_box(0);
    v___x_477_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_478_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_478_, 0, v___x_477_);
    lean_ctor_set(v___x_478_, 1, v___x_476_);
    return v___x_478_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg()
-> *mut LeanObject {
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0);
    v___x_481_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_481_, 0, v___x_480_);
    return v___x_481_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___boxed(
    mut v___y_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_483_: *mut LeanObject = core::ptr::null_mut();
    v_res_483_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
    return v_res_483_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(
    mut v_00_u03b1_484_: *mut LeanObject,
    mut v___y_485_: *mut LeanObject,
    mut v___y_486_: *mut LeanObject,
    mut v___y_487_: *mut LeanObject,
    mut v___y_488_: *mut LeanObject,
    mut v___y_489_: *mut LeanObject,
    mut v___y_490_: *mut LeanObject,
    mut v___y_491_: *mut LeanObject,
    mut v___y_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
    return v___x_494_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___boxed(
    mut v_00_u03b1_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
    mut v___y_499_: *mut LeanObject,
    mut v___y_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
    mut v___y_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_505_: *mut LeanObject = core::ptr::null_mut();
    v_res_505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(
        v_00_u03b1_495_,
        v___y_496_,
        v___y_497_,
        v___y_498_,
        v___y_499_,
        v___y_500_,
        v___y_501_,
        v___y_502_,
        v___y_503_,
    );
    lean_dec(v___y_503_);
    lean_dec_ref(v___y_502_);
    lean_dec(v___y_501_);
    lean_dec_ref(v___y_500_);
    lean_dec(v___y_499_);
    lean_dec_ref(v___y_498_);
    lean_dec(v___y_497_);
    lean_dec_ref(v___y_496_);
    return v_res_505_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__0(
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
    mut v___y_508_: *mut LeanObject,
    mut v___y_509_: *mut LeanObject,
    mut v___y_510_: *mut LeanObject,
    mut v___y_511_: *mut LeanObject,
    mut v___y_512_: *mut LeanObject,
    mut v___y_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_525_: u8 = 0;
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_529_: u8 = 0;
    let mut v_a_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_533_: u8 = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_515_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_507_, v___y_510_, v___y_511_, v___y_512_, v___y_513_,
                );
                if lean_obj_tag(v___x_515_) == 0 {
                    v_a_516_ = lean_ctor_get(v___x_515_, 0);
                    lean_inc(v_a_516_);
                    lean_dec_ref_known(v___x_515_, 1);
                    v___x_517_ = l_Lean_MVarId_applySymm(
                        v_a_516_, v___y_510_, v___y_511_, v___y_512_, v___y_513_,
                    );
                    if lean_obj_tag(v___x_517_) == 0 {
                        v_a_518_ = lean_ctor_get(v___x_517_, 0);
                        lean_inc(v_a_518_);
                        lean_dec_ref_known(v___x_517_, 1);
                        v___x_519_ = lean_box(0);
                        v___x_520_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_520_, 0, v_a_518_);
                        lean_ctor_set(v___x_520_, 1, v___x_519_);
                        v___x_521_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_520_, v___y_507_, v___y_510_, v___y_511_, v___y_512_, v___y_513_,
                        );
                        return v___x_521_;
                    } else {
                        v_a_522_ = lean_ctor_get(v___x_517_, 0);
                        v_isSharedCheck_529_ = (!lean_is_exclusive(v___x_517_)) as u8;
                        if v_isSharedCheck_529_ == 0 {
                            v___x_524_ = v___x_517_;
                            v_isShared_525_ = v_isSharedCheck_529_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_522_);
                            lean_dec(v___x_517_);
                            v___x_524_ = lean_box(0);
                            v_isShared_525_ = v_isSharedCheck_529_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_530_ = lean_ctor_get(v___x_515_, 0);
                    v_isSharedCheck_537_ = (!lean_is_exclusive(v___x_515_)) as u8;
                    if v_isSharedCheck_537_ == 0 {
                        v___x_532_ = v___x_515_;
                        v_isShared_533_ = v_isSharedCheck_537_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_530_);
                        lean_dec(v___x_515_);
                        v___x_532_ = lean_box(0);
                        v_isShared_533_ = v_isSharedCheck_537_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_525_ == 0 {
                    v___x_527_ = v___x_524_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
                    v___x_527_ = v_reuseFailAlloc_528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_527_;
            }
            3 => {
                if v_isShared_533_ == 0 {
                    v___x_535_ = v___x_532_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
                    v___x_535_ = v_reuseFailAlloc_536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__0___boxed(
    mut v___y_538_: *mut LeanObject,
    mut v___y_539_: *mut LeanObject,
    mut v___y_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
    mut v___y_542_: *mut LeanObject,
    mut v___y_543_: *mut LeanObject,
    mut v___y_544_: *mut LeanObject,
    mut v___y_545_: *mut LeanObject,
    mut v___y_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_547_: *mut LeanObject = core::ptr::null_mut();
    v_res_547_ = l_Lean_Elab_Tactic_evalSymm___lam__0(
        v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_,
        v___y_545_,
    );
    lean_dec(v___y_545_);
    lean_dec_ref(v___y_544_);
    lean_dec(v___y_543_);
    lean_dec_ref(v___y_542_);
    lean_dec(v___y_541_);
    lean_dec_ref(v___y_540_);
    lean_dec(v___y_539_);
    lean_dec_ref(v___y_538_);
    return v_res_547_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__1(
    mut v___f_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
    mut v___y_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
    mut v___y_552_: *mut LeanObject,
    mut v___y_553_: *mut LeanObject,
    mut v___y_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_,
        v___y_555_, v___y_556_,
    );
    return v___x_558_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__1___boxed(
    mut v___f_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
    mut v___y_562_: *mut LeanObject,
    mut v___y_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
    mut v___y_565_: *mut LeanObject,
    mut v___y_566_: *mut LeanObject,
    mut v___y_567_: *mut LeanObject,
    mut v___y_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_569_: *mut LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Lean_Elab_Tactic_evalSymm___lam__1(
        v___f_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_,
        v___y_566_, v___y_567_,
    );
    lean_dec(v___y_567_);
    lean_dec_ref(v___y_566_);
    lean_dec(v___y_565_);
    lean_dec_ref(v___y_564_);
    lean_dec(v___y_563_);
    lean_dec_ref(v___y_562_);
    lean_dec(v___y_561_);
    lean_dec_ref(v___y_560_);
    return v_res_569_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(
    mut v_msgData_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v___x_576_ = lean_st_ref_get(v___y_574_);
    v_env_577_ = lean_ctor_get(v___x_576_, 0);
    lean_inc_ref(v_env_577_);
    lean_dec(v___x_576_);
    v___x_578_ = lean_st_ref_get(v___y_572_);
    v_mctx_579_ = lean_ctor_get(v___x_578_, 0);
    lean_inc_ref(v_mctx_579_);
    lean_dec(v___x_578_);
    v_lctx_580_ = lean_ctor_get(v___y_571_, 2);
    v_options_581_ = lean_ctor_get(v___y_573_, 2);
    lean_inc_ref(v_options_581_);
    lean_inc_ref(v_lctx_580_);
    v___x_582_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_582_, 0, v_env_577_);
    lean_ctor_set(v___x_582_, 1, v_mctx_579_);
    lean_ctor_set(v___x_582_, 2, v_lctx_580_);
    lean_ctor_set(v___x_582_, 3, v_options_581_);
    v___x_583_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_583_, 0, v___x_582_);
    lean_ctor_set(v___x_583_, 1, v_msgData_570_);
    v___x_584_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_584_, 0, v___x_583_);
    return v___x_584_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0___boxed(
    mut v_msgData_585_: *mut LeanObject,
    mut v___y_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_591_: *mut LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(v_msgData_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
    lean_dec(v___y_589_);
    lean_dec_ref(v___y_588_);
    lean_dec(v___y_587_);
    lean_dec_ref(v___y_586_);
    return v_res_591_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(
    mut v_msg_592_: *mut LeanObject,
    mut v___y_593_: *mut LeanObject,
    mut v___y_594_: *mut LeanObject,
    mut v___y_595_: *mut LeanObject,
    mut v___y_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_598_ = lean_ctor_get(v___y_595_, 5);
                v___x_599_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(v_msg_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
                v_a_600_ = lean_ctor_get(v___x_599_, 0);
                v_isSharedCheck_608_ = (!lean_is_exclusive(v___x_599_)) as u8;
                if v_isSharedCheck_608_ == 0 {
                    v___x_602_ = v___x_599_;
                    v_isShared_603_ = v_isSharedCheck_608_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_600_);
                    lean_dec(v___x_599_);
                    v___x_602_ = lean_box(0);
                    v_isShared_603_ = v_isSharedCheck_608_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_598_);
                v___x_604_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_604_, 0, v_ref_598_);
                lean_ctor_set(v___x_604_, 1, v_a_600_);
                if v_isShared_603_ == 0 {
                    lean_ctor_set_tag(v___x_602_, 1);
                    lean_ctor_set(v___x_602_, 0, v___x_604_);
                    v___x_606_ = v___x_602_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
                    v___x_606_ = v_reuseFailAlloc_607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg___boxed(
    mut v_msg_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
    mut v___y_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_615_: *mut LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(
        v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_,
    );
    lean_dec(v___y_613_);
    lean_dec_ref(v___y_612_);
    lean_dec(v___y_611_);
    lean_dec_ref(v___y_610_);
    return v_res_615_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1() -> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0;
    v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
    return v___x_618_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__2(
    mut v_x_619_: *mut LeanObject,
    mut v___y_620_: *mut LeanObject,
    mut v___y_621_: *mut LeanObject,
    mut v___y_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_629_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1,
    );
    v___x_630_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(
        v___x_629_, v___y_624_, v___y_625_, v___y_626_, v___y_627_,
    );
    return v___x_630_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__2___boxed(
    mut v_x_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
    mut v___y_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_641_: *mut LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lean_Elab_Tactic_evalSymm___lam__2(
        v_x_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_,
        v___y_638_, v___y_639_,
    );
    lean_dec(v___y_639_);
    lean_dec_ref(v___y_638_);
    lean_dec(v___y_637_);
    lean_dec_ref(v___y_636_);
    lean_dec(v___y_635_);
    lean_dec_ref(v___y_634_);
    lean_dec(v___y_633_);
    lean_dec_ref(v___y_632_);
    lean_dec(v_x_631_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__3(
    mut v_h_642_: *mut LeanObject,
    mut v___y_643_: *mut LeanObject,
    mut v___y_644_: *mut LeanObject,
    mut v___y_645_: *mut LeanObject,
    mut v___y_646_: *mut LeanObject,
    mut v___y_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
    mut v___y_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_a_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_652_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_644_, v___y_647_, v___y_648_, v___y_649_, v___y_650_,
                );
                if lean_obj_tag(v___x_652_) == 0 {
                    v_a_653_ = lean_ctor_get(v___x_652_, 0);
                    lean_inc(v_a_653_);
                    lean_dec_ref_known(v___x_652_, 1);
                    v___x_654_ = l_Lean_MVarId_applySymmAt(
                        v_h_642_, v_a_653_, v___y_647_, v___y_648_, v___y_649_, v___y_650_,
                    );
                    if lean_obj_tag(v___x_654_) == 0 {
                        v_a_655_ = lean_ctor_get(v___x_654_, 0);
                        lean_inc(v_a_655_);
                        lean_dec_ref_known(v___x_654_, 1);
                        v___x_656_ = lean_box(0);
                        v___x_657_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_657_, 0, v_a_655_);
                        lean_ctor_set(v___x_657_, 1, v___x_656_);
                        v___x_658_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_657_, v___y_644_, v___y_647_, v___y_648_, v___y_649_, v___y_650_,
                        );
                        return v___x_658_;
                    } else {
                        v_a_659_ = lean_ctor_get(v___x_654_, 0);
                        v_isSharedCheck_666_ = (!lean_is_exclusive(v___x_654_)) as u8;
                        if v_isSharedCheck_666_ == 0 {
                            v___x_661_ = v___x_654_;
                            v_isShared_662_ = v_isSharedCheck_666_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_659_);
                            lean_dec(v___x_654_);
                            v___x_661_ = lean_box(0);
                            v_isShared_662_ = v_isSharedCheck_666_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_h_642_);
                    v_a_667_ = lean_ctor_get(v___x_652_, 0);
                    v_isSharedCheck_674_ = (!lean_is_exclusive(v___x_652_)) as u8;
                    if v_isSharedCheck_674_ == 0 {
                        v___x_669_ = v___x_652_;
                        v_isShared_670_ = v_isSharedCheck_674_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_667_);
                        lean_dec(v___x_652_);
                        v___x_669_ = lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_674_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_662_ == 0 {
                    v___x_664_ = v___x_661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
                    v___x_664_ = v_reuseFailAlloc_665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_664_;
            }
            3 => {
                if v_isShared_670_ == 0 {
                    v___x_672_ = v___x_669_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
                    v___x_672_ = v_reuseFailAlloc_673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__3___boxed(
    mut v_h_675_: *mut LeanObject,
    mut v___y_676_: *mut LeanObject,
    mut v___y_677_: *mut LeanObject,
    mut v___y_678_: *mut LeanObject,
    mut v___y_679_: *mut LeanObject,
    mut v___y_680_: *mut LeanObject,
    mut v___y_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
    mut v___y_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_685_: *mut LeanObject = core::ptr::null_mut();
    v_res_685_ = l_Lean_Elab_Tactic_evalSymm___lam__3(
        v_h_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_,
        v___y_682_, v___y_683_,
    );
    lean_dec(v___y_683_);
    lean_dec_ref(v___y_682_);
    lean_dec(v___y_681_);
    lean_dec_ref(v___y_680_);
    lean_dec(v___y_679_);
    lean_dec_ref(v___y_678_);
    lean_dec(v___y_677_);
    lean_dec_ref(v___y_676_);
    return v_res_685_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__4(
    mut v_h_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___f_696_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSymm___lam__3___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___f_696_, 0, v_h_686_);
    v___x_697_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_696_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_,
        v___y_693_, v___y_694_,
    );
    return v___x_697_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___lam__4___boxed(
    mut v_h_698_: *mut LeanObject,
    mut v___y_699_: *mut LeanObject,
    mut v___y_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Lean_Elab_Tactic_evalSymm___lam__4(
        v_h_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_,
        v___y_705_, v___y_706_,
    );
    lean_dec(v___y_706_);
    lean_dec_ref(v___y_705_);
    lean_dec(v___y_704_);
    lean_dec_ref(v___y_703_);
    lean_dec(v___y_702_);
    lean_dec_ref(v___y_701_);
    lean_dec(v___y_700_);
    lean_dec_ref(v___y_699_);
    return v_res_708_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm(
    mut v_stx_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    v___x_735_ = l_Lean_Elab_Tactic_evalSymm___closed__4;
    lean_inc(v_stx_725_);
    v___x_736_ = l_Lean_Syntax_isOfKind(v_stx_725_, v___x_735_);
    if v___x_736_ == 0 {
        let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_725_);
        v___x_737_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg(
            );
        return v___x_737_;
    } else {
        let mut v_atTarget_738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_739_: *mut LeanObject = core::ptr::null_mut();
        let mut v_atHyp_740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
        v_atTarget_738_ = l_Lean_Elab_Tactic_evalSymm___closed__6;
        v___f_739_ = l_Lean_Elab_Tactic_evalSymm___closed__7;
        v_atHyp_740_ = l_Lean_Elab_Tactic_evalSymm___closed__8;
        v___x_741_ = lean_unsigned_to_nat(1);
        v___x_742_ = l_Lean_Syntax_getArg(v_stx_725_, v___x_741_);
        lean_dec(v_stx_725_);
        v___x_743_ = l_Lean_Syntax_getOptional_x3f(v___x_742_);
        lean_dec(v___x_742_);
        if lean_obj_tag(v___x_743_) == 0 {
            let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
            v___x_744_ = l_Lean_Elab_Tactic_evalSymm___closed__9;
            v___x_745_ = lean_alloc_ctor(1, 1, (1) as u32);
            lean_ctor_set(v___x_745_, 0, v___x_744_);
            lean_ctor_set_uint8(
                v___x_745_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                v___x_736_,
            );
            v___x_746_ = l_Lean_Elab_Tactic_withLocation(
                v___x_745_,
                v_atHyp_740_,
                v_atTarget_738_,
                v___f_739_,
                v_a_726_,
                v_a_727_,
                v_a_728_,
                v_a_729_,
                v_a_730_,
                v_a_731_,
                v_a_732_,
                v_a_733_,
            );
            lean_dec_ref_known(v___x_745_, 1);
            return v___x_746_;
        } else {
            let mut v_val_747_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
            v_val_747_ = lean_ctor_get(v___x_743_, 0);
            lean_inc(v_val_747_);
            lean_dec_ref_known(v___x_743_, 1);
            v___x_748_ = l_Lean_Elab_Tactic_expandLocation(v_val_747_);
            lean_dec(v_val_747_);
            v___x_749_ = l_Lean_Elab_Tactic_withLocation(
                v___x_748_,
                v_atHyp_740_,
                v_atTarget_738_,
                v___f_739_,
                v_a_726_,
                v_a_727_,
                v_a_728_,
                v_a_729_,
                v_a_730_,
                v_a_731_,
                v_a_732_,
                v_a_733_,
            );
            lean_dec(v___x_748_);
            return v___x_749_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymm___boxed(
    mut v_stx_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
    mut v_a_753_: *mut LeanObject,
    mut v_a_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_760_: *mut LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_Elab_Tactic_evalSymm(
        v_stx_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_,
    );
    lean_dec(v_a_758_);
    lean_dec_ref(v_a_757_);
    lean_dec(v_a_756_);
    lean_dec_ref(v_a_755_);
    lean_dec(v_a_754_);
    lean_dec_ref(v_a_753_);
    lean_dec(v_a_752_);
    lean_dec_ref(v_a_751_);
    return v_res_760_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(
    mut v_00_u03b1_761_: *mut LeanObject,
    mut v_msg_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(
        v_msg_762_, v___y_767_, v___y_768_, v___y_769_, v___y_770_,
    );
    return v___x_772_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___boxed(
    mut v_00_u03b1_773_: *mut LeanObject,
    mut v_msg_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(
        v_00_u03b1_773_,
        v_msg_774_,
        v___y_775_,
        v___y_776_,
        v___y_777_,
        v___y_778_,
        v___y_779_,
        v___y_780_,
        v___y_781_,
        v___y_782_,
    );
    lean_dec(v___y_782_);
    lean_dec_ref(v___y_781_);
    lean_dec(v___y_780_);
    lean_dec_ref(v___y_779_);
    lean_dec(v___y_778_);
    lean_dec_ref(v___y_777_);
    lean_dec(v___y_776_);
    lean_dec_ref(v___y_775_);
    return v_res_784_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1()
-> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_794_ = l_Lean_Elab_Tactic_evalSymm___closed__4;
    v___x_795_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2;
    v___x_796_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSymm___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_797_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_793_, v___x_794_, v___x_795_, v___x_796_,
    );
    return v___x_797_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___boxed(
    mut v_a_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_799_: *mut LeanObject = core::ptr::null_mut();
    v_res_799_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
    return v_res_799_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3()
-> *mut LeanObject {
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2;
    v___x_827_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6;
    v___x_828_ = l_Lean_addBuiltinDeclarationRanges(v___x_826_, v___x_827_);
    return v___x_828_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___boxed(
    mut v_a_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
    return v_res_830_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
    mut v___y_835_: *mut LeanObject,
    mut v___y_836_: *mut LeanObject,
    mut v___y_837_: *mut LeanObject,
    mut v___y_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_a_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_840_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_832_, v___y_835_, v___y_836_, v___y_837_, v___y_838_,
                );
                if lean_obj_tag(v___x_840_) == 0 {
                    v_a_841_ = lean_ctor_get(v___x_840_, 0);
                    lean_inc(v_a_841_);
                    lean_dec_ref_known(v___x_840_, 1);
                    v___x_842_ = l_Lean_MVarId_symmSaturate(
                        v_a_841_, v___y_835_, v___y_836_, v___y_837_, v___y_838_,
                    );
                    if lean_obj_tag(v___x_842_) == 0 {
                        v_a_843_ = lean_ctor_get(v___x_842_, 0);
                        lean_inc(v_a_843_);
                        lean_dec_ref_known(v___x_842_, 1);
                        v___x_844_ = lean_box(0);
                        v___x_845_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_845_, 0, v_a_843_);
                        lean_ctor_set(v___x_845_, 1, v___x_844_);
                        v___x_846_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_845_, v___y_832_, v___y_835_, v___y_836_, v___y_837_, v___y_838_,
                        );
                        return v___x_846_;
                    } else {
                        v_a_847_ = lean_ctor_get(v___x_842_, 0);
                        v_isSharedCheck_854_ = (!lean_is_exclusive(v___x_842_)) as u8;
                        if v_isSharedCheck_854_ == 0 {
                            v___x_849_ = v___x_842_;
                            v_isShared_850_ = v_isSharedCheck_854_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_847_);
                            lean_dec(v___x_842_);
                            v___x_849_ = lean_box(0);
                            v_isShared_850_ = v_isSharedCheck_854_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_855_ = lean_ctor_get(v___x_840_, 0);
                    v_isSharedCheck_862_ = (!lean_is_exclusive(v___x_840_)) as u8;
                    if v_isSharedCheck_862_ == 0 {
                        v___x_857_ = v___x_840_;
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_855_);
                        lean_dec(v___x_840_);
                        v___x_857_ = lean_box(0);
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_850_ == 0 {
                    v___x_852_ = v___x_849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
                    v___x_852_ = v_reuseFailAlloc_853_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_852_;
            }
            3 => {
                if v_isShared_858_ == 0 {
                    v___x_860_ = v___x_857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
                    v___x_860_ = v_reuseFailAlloc_861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymmSaturate___lam__0___boxed(
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_872_: *mut LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(
        v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_,
        v___y_870_,
    );
    lean_dec(v___y_870_);
    lean_dec_ref(v___y_869_);
    lean_dec(v___y_868_);
    lean_dec_ref(v___y_867_);
    lean_dec(v___y_866_);
    lean_dec_ref(v___y_865_);
    lean_dec(v___y_864_);
    lean_dec_ref(v___y_863_);
    return v_res_872_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymmSaturate(
    mut v_stx_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
    mut v_a_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u8 = 0;
    v___x_890_ = l_Lean_Elab_Tactic_evalSymmSaturate___closed__1;
    v___x_891_ = l_Lean_Syntax_isOfKind(v_stx_880_, v___x_890_);
    if v___x_891_ == 0 {
        let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
        v___x_892_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg(
            );
        return v___x_892_;
    } else {
        let mut v___f_893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
        v___f_893_ = l_Lean_Elab_Tactic_evalSymmSaturate___closed__2;
        v___x_894_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_893_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_,
            v_a_888_,
        );
        return v___x_894_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSymmSaturate___boxed(
    mut v_stx_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Elab_Tactic_evalSymmSaturate(
        v_stx_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_,
    );
    lean_dec(v_a_903_);
    lean_dec_ref(v_a_902_);
    lean_dec(v_a_901_);
    lean_dec_ref(v_a_900_);
    lean_dec(v_a_899_);
    lean_dec_ref(v_a_898_);
    lean_dec(v_a_897_);
    lean_dec_ref(v_a_896_);
    return v_res_905_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1()
-> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_914_ = l_Lean_Elab_Tactic_evalSymmSaturate___closed__1;
    v___x_915_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1;
    v___x_916_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSymmSaturate___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_917_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_913_, v___x_914_, v___x_915_, v___x_916_,
    );
    return v___x_917_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___boxed(
    mut v_a_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
    return v_res_919_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3()
-> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v___x_946_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1;
    v___x_947_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6;
    v___x_948_ = l_Lean_addBuiltinDeclarationRanges(v___x_946_, v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___boxed(
    mut v_a_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_res_950_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
    return v_res_950_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Symm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Symm(builtin);
}
