// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Change
// Imports: Lean.Elab.Tactic.Change Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Change::{
    initialize_Lean_Elab_Tactic_Change, l_Lean_Elab_Tactic_elabChange,
    l_Lean_Elab_Tactic_elabChangeDefaultError___boxed, runtime_initialize_Lean_Elab_Tactic_Change,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_filterOldMVars___redArg, l_Lean_Elab_Tactic_logUnassignedAndAbort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_elabChangeDefaultError___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value: LeanStringObject<5> =
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
        m_data: [67, 111, 110, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value: LeanStringObject<7> =
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
        m_data: [99, 104, 97, 110, 103, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value)
                as *mut LeanObject,
            1203263152968118357 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 67, 104, 97, 110, 103, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value) as *mut LeanObject,12854273918554071889 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value) as *mut LeanObject,((( 53 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    v___x_185_ = lean_box(0);
    v___x_186_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_187_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_187_, 0, v___x_186_);
    lean_ctor_set(v___x_187_, 1, v___x_185_);
    return v___x_187_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v___x_189_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0);
    v___x_190_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_190_, 0, v___x_189_);
    return v___x_190_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___boxed(
    mut v___y_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_192_: *mut LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
    return v_res_192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(
    mut v_00_u03b1_193_: *mut LeanObject,
    mut v___y_194_: *mut LeanObject,
    mut v___y_195_: *mut LeanObject,
    mut v___y_196_: *mut LeanObject,
    mut v___y_197_: *mut LeanObject,
    mut v___y_198_: *mut LeanObject,
    mut v___y_199_: *mut LeanObject,
    mut v___y_200_: *mut LeanObject,
    mut v___y_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    v___x_203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
    return v___x_203_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___boxed(
    mut v_00_u03b1_204_: *mut LeanObject,
    mut v___y_205_: *mut LeanObject,
    mut v___y_206_: *mut LeanObject,
    mut v___y_207_: *mut LeanObject,
    mut v___y_208_: *mut LeanObject,
    mut v___y_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v___y_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_214_: *mut LeanObject = core::ptr::null_mut();
    v_res_214_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(
            v_00_u03b1_204_,
            v___y_205_,
            v___y_206_,
            v___y_207_,
            v___y_208_,
            v___y_209_,
            v___y_210_,
            v___y_211_,
            v___y_212_,
        );
    lean_dec(v___y_212_);
    lean_dec_ref(v___y_211_);
    lean_dec(v___y_210_);
    lean_dec_ref(v___y_209_);
    lean_dec(v___y_208_);
    lean_dec_ref(v___y_207_);
    lean_dec(v___y_206_);
    lean_dec_ref(v___y_205_);
    return v_res_214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___lam__0(
    mut v_e_216_: *mut LeanObject,
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
    let mut v_a_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut v_a_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_251_: u8 = 0;
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut v_a_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_259_: u8 = 0;
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut v_a_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_226_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                );
                if lean_obj_tag(v___x_226_) == 0 {
                    v_a_227_ = lean_ctor_get(v___x_226_, 0);
                    lean_inc(v_a_227_);
                    lean_dec_ref_known(v___x_226_, 1);
                    v___x_228_ = lean_st_ref_get(v___y_222_);
                    v___x_229_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0;
                    v___x_230_ = l_Lean_Elab_Tactic_elabChange(
                        v_a_227_, v_e_216_, v___x_229_, v___y_217_, v___y_218_, v___y_219_,
                        v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                    );
                    if lean_obj_tag(v___x_230_) == 0 {
                        v_a_231_ = lean_ctor_get(v___x_230_, 0);
                        lean_inc_n(v_a_231_, 2);
                        lean_dec_ref_known(v___x_230_, 1);
                        v___x_232_ = l_Lean_Meta_getMVars(
                            v_a_231_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                        );
                        if lean_obj_tag(v___x_232_) == 0 {
                            v_mctx_233_ = lean_ctor_get(v___x_228_, 0);
                            lean_inc_ref(v_mctx_233_);
                            lean_dec(v___x_228_);
                            v_a_234_ = lean_ctor_get(v___x_232_, 0);
                            lean_inc(v_a_234_);
                            lean_dec_ref_known(v___x_232_, 1);
                            v_mvarCounter_235_ = lean_ctor_get(v_mctx_233_, 3);
                            lean_inc(v_mvarCounter_235_);
                            lean_dec_ref(v_mctx_233_);
                            v___x_236_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
                                v_a_234_,
                                v_mvarCounter_235_,
                                v___y_222_,
                            );
                            lean_dec(v_mvarCounter_235_);
                            lean_dec(v_a_234_);
                            if lean_obj_tag(v___x_236_) == 0 {
                                v_a_237_ = lean_ctor_get(v___x_236_, 0);
                                lean_inc(v_a_237_);
                                lean_dec_ref_known(v___x_236_, 1);
                                v___x_238_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
                                    v_a_237_, v___y_217_, v___y_218_, v___y_219_, v___y_220_,
                                    v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                                );
                                lean_dec(v_a_237_);
                                if lean_obj_tag(v___x_238_) == 0 {
                                    lean_dec_ref_known(v___x_238_, 1);
                                    v___x_239_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_231_, v___y_217_, v___y_218_, v___y_219_, v___y_220_,
                                        v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                                    );
                                    return v___x_239_;
                                } else {
                                    lean_dec(v_a_231_);
                                    return v___x_238_;
                                }
                            } else {
                                lean_dec(v_a_231_);
                                v_a_240_ = lean_ctor_get(v___x_236_, 0);
                                v_isSharedCheck_247_ = (!lean_is_exclusive(v___x_236_)) as u8;
                                if v_isSharedCheck_247_ == 0 {
                                    v___x_242_ = v___x_236_;
                                    v_isShared_243_ = v_isSharedCheck_247_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_240_);
                                    lean_dec(v___x_236_);
                                    v___x_242_ = lean_box(0);
                                    v_isShared_243_ = v_isSharedCheck_247_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_231_);
                            lean_dec(v___x_228_);
                            v_a_248_ = lean_ctor_get(v___x_232_, 0);
                            v_isSharedCheck_255_ = (!lean_is_exclusive(v___x_232_)) as u8;
                            if v_isSharedCheck_255_ == 0 {
                                v___x_250_ = v___x_232_;
                                v_isShared_251_ = v_isSharedCheck_255_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_248_);
                                lean_dec(v___x_232_);
                                v___x_250_ = lean_box(0);
                                v_isShared_251_ = v_isSharedCheck_255_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_228_);
                        v_a_256_ = lean_ctor_get(v___x_230_, 0);
                        v_isSharedCheck_263_ = (!lean_is_exclusive(v___x_230_)) as u8;
                        if v_isSharedCheck_263_ == 0 {
                            v___x_258_ = v___x_230_;
                            v_isShared_259_ = v_isSharedCheck_263_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_256_);
                            lean_dec(v___x_230_);
                            v___x_258_ = lean_box(0);
                            v_isShared_259_ = v_isSharedCheck_263_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_e_216_);
                    v_a_264_ = lean_ctor_get(v___x_226_, 0);
                    v_isSharedCheck_271_ = (!lean_is_exclusive(v___x_226_)) as u8;
                    if v_isSharedCheck_271_ == 0 {
                        v___x_266_ = v___x_226_;
                        v_isShared_267_ = v_isSharedCheck_271_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_264_);
                        lean_dec(v___x_226_);
                        v___x_266_ = lean_box(0);
                        v_isShared_267_ = v_isSharedCheck_271_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_243_ == 0 {
                    v___x_245_ = v___x_242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
                    v___x_245_ = v_reuseFailAlloc_246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_245_;
            }
            3 => {
                if v_isShared_251_ == 0 {
                    v___x_253_ = v___x_250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
                    v___x_253_ = v_reuseFailAlloc_254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_253_;
            }
            5 => {
                if v_isShared_259_ == 0 {
                    v___x_261_ = v___x_258_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
                    v___x_261_ = v_reuseFailAlloc_262_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_261_;
            }
            7 => {
                if v_isShared_267_ == 0 {
                    v___x_269_ = v___x_266_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
                    v___x_269_ = v_reuseFailAlloc_270_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed(
    mut v_e_272_: *mut LeanObject,
    mut v___y_273_: *mut LeanObject,
    mut v___y_274_: *mut LeanObject,
    mut v___y_275_: *mut LeanObject,
    mut v___y_276_: *mut LeanObject,
    mut v___y_277_: *mut LeanObject,
    mut v___y_278_: *mut LeanObject,
    mut v___y_279_: *mut LeanObject,
    mut v___y_280_: *mut LeanObject,
    mut v___y_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_282_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0(
        v_e_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_,
        v___y_279_, v___y_280_,
    );
    lean_dec(v___y_280_);
    lean_dec_ref(v___y_279_);
    lean_dec(v___y_278_);
    lean_dec_ref(v___y_277_);
    lean_dec(v___y_276_);
    lean_dec_ref(v___y_275_);
    lean_dec(v___y_274_);
    lean_dec_ref(v___y_273_);
    return v_res_282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange(
    mut v_stx_294_: *mut LeanObject,
    mut v_a_295_: *mut LeanObject,
    mut v_a_296_: *mut LeanObject,
    mut v_a_297_: *mut LeanObject,
    mut v_a_298_: *mut LeanObject,
    mut v_a_299_: *mut LeanObject,
    mut v_a_300_: *mut LeanObject,
    mut v_a_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: u8 = 0;
    v___x_304_ = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
    lean_inc(v_stx_294_);
    v___x_305_ = l_Lean_Syntax_isOfKind(v_stx_294_, v___x_304_);
    if v___x_305_ == 0 {
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_294_);
        v___x_306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
        return v___x_306_;
    } else {
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v_e_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        v___x_307_ = lean_unsigned_to_nat(1);
        v_e_308_ = l_Lean_Syntax_getArg(v_stx_294_, v___x_307_);
        lean_dec(v_stx_294_);
        v___f_309_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed as *mut core::ffi::c_void,
            10,
            1,
        );
        lean_closure_set(v___f_309_, 0, v_e_308_);
        v___x_310_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_309_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_,
            v_a_302_,
        );
        return v___x_310_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___boxed(
    mut v_stx_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
    mut v_a_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_a_316_: *mut LeanObject,
    mut v_a_317_: *mut LeanObject,
    mut v_a_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_321_: *mut LeanObject = core::ptr::null_mut();
    v_res_321_ = l_Lean_Elab_Tactic_Conv_evalChange(
        v_stx_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_,
    );
    lean_dec(v_a_319_);
    lean_dec_ref(v_a_318_);
    lean_dec(v_a_317_);
    lean_dec_ref(v_a_316_);
    lean_dec(v_a_315_);
    lean_dec_ref(v_a_314_);
    lean_dec(v_a_313_);
    lean_dec_ref(v_a_312_);
    return v_res_321_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1()
-> *mut LeanObject {
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_331_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_332_ = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
    v___x_333_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
    v___x_334_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalChange___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_331_, v___x_332_, v___x_333_, v___x_334_,
    );
    return v___x_335_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___boxed(
    mut v_a_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
    return v_res_337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3()
-> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
    v___x_365_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6;
    v___x_366_ = l_Lean_addBuiltinDeclarationRanges(v___x_364_, v___x_365_);
    return v___x_366_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___boxed(
    mut v_a_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_368_: *mut LeanObject = core::ptr::null_mut();
    v_res_368_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
    return v_res_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Change(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Change(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Change(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Change(builtin);
}
