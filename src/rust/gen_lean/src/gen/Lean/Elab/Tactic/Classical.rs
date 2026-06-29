// Lean compiler output
// Module: Lean.Elab.Tactic.Classical
// Imports: Lean.Elab.Tactic.Basic
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_append___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoTree_substitute;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_evalTactic___boxed,
    l_Lean_Elab_Tactic_tacticElabAttribute, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go;
use crate::r#gen::Lean::Elab::Term::l_Lean_Elab_addBuiltinIncrementalElab;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Language::Basic::l_Lean_Language_SnapshotTask_cancelRec___redArg;
use crate::r#gen::Lean::Meta::Instances::{
    l_Lean_Meta_addInstance, l_Lean_Meta_addInstance___boxed, l_Lean_Meta_instanceExtension,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_popScope, l_Lean_ScopedEnvExtension_popScope___redArg,
    l_Lean_ScopedEnvExtension_pushScope, l_Lean_ScopedEnvExtension_pushScope___redArg,
};
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_eqWithInfoAndTraceReuse, l_Lean_Syntax_hasMissing};
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        112, 114, 111, 112, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10854111772627758120 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        4643704380461739942 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_addInstance___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((10 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_classical___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalClassical___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalTactic___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalClassical___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalClassical___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut crate::leanh::LeanObject,1538718060909595165 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut crate::leanh::LeanObject,3595078106460476937 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0(
    mut v_x_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1318_ = crate::leanh::lean_ctor_get(v_x_1317_, 0);
    crate::leanh::lean_inc(v_fst_1318_);
    return v_fst_1318_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed(
    mut v_x_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_Elab_Tactic_classical___redArg___lam__0(v_x_1319_);
    crate::leanh::lean_dec_ref(v_x_1319_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1(
    mut v___x_1321_: *mut crate::leanh::LeanObject,
    mut v_x_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_1321_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed(
    mut v___x_1323_: *mut crate::leanh::LeanObject,
    mut v_x_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lean_Elab_Tactic_classical___redArg___lam__1(v___x_1323_, v_x_1324_);
    crate::leanh::lean_dec(v_x_1324_);
    crate::leanh::lean_dec(v___x_1323_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__2(
    mut v_toFunctor_1326_: *mut crate::leanh::LeanObject,
    mut v___x_1327_: *mut crate::leanh::LeanObject,
    mut v_modifyEnv_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
    mut v_t_1330_: *mut crate::leanh::LeanObject,
    mut v___f_1331_: *mut crate::leanh::LeanObject,
    mut v_____r_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1333_ = crate::leanh::lean_ctor_get(v_toFunctor_1326_, 0);
    crate::leanh::lean_inc(v_map_1333_);
    crate::leanh::lean_dec_ref(v_toFunctor_1326_);
    v___x_1334_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_popScope as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1334_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1334_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1334_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1334_, 3, v___x_1327_);
    v___x_1335_ = crate::leanh::lean_apply_1(v_modifyEnv_1328_, v___x_1334_);
    v___f_1336_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1336_, 0, v___x_1335_);
    v_y_1337_ = crate::leanh::lean_apply_4(
        v_inst_1329_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_t_1330_,
        v___f_1336_,
    );
    v___x_1338_ = crate::leanh::lean_apply_4(
        v_map_1333_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1331_,
        v_y_1337_,
    );
    return v___x_1338_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__3(
    mut v_inst_1349_: *mut crate::leanh::LeanObject,
    mut v_toBind_1350_: *mut crate::leanh::LeanObject,
    mut v___f_1351_: *mut crate::leanh::LeanObject,
    mut v_____r_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3;
    v___x_1354_ = crate::leanh::lean_apply_2(v_inst_1349_, crate::leanh::lean_box(0), v___x_1353_);
    v___x_1355_ = crate::leanh::lean_apply_4(
        v_toBind_1350_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1354_,
        v___f_1351_,
    );
    return v___x_1355_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lean_Meta_instanceExtension;
    v___x_1358_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_pushScope as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_1358_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1358_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1358_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1358_, 3, v___x_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg(
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
    mut v_inst_1360_: *mut crate::leanh::LeanObject,
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
    mut v_t_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1364_ = crate::leanh::lean_ctor_get(v_inst_1359_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1364_);
    v_toBind_1365_ = crate::leanh::lean_ctor_get(v_inst_1359_, 1);
    crate::leanh::lean_inc_n(v_toBind_1365_, 2);
    crate::leanh::lean_dec_ref(v_inst_1359_);
    v_modifyEnv_1366_ = crate::leanh::lean_ctor_get(v_inst_1360_, 1);
    crate::leanh::lean_inc_n(v_modifyEnv_1366_, 2);
    crate::leanh::lean_dec_ref(v_inst_1360_);
    v_toFunctor_1367_ = crate::leanh::lean_ctor_get(v_toApplicative_1364_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1367_);
    crate::leanh::lean_dec_ref(v_toApplicative_1364_);
    v___f_1368_ = l_Lean_Elab_Tactic_classical___redArg___closed__0;
    v___x_1369_ = l_Lean_Meta_instanceExtension;
    v___x_1370_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_classical___redArg___closed__1,
    );
    v___x_1371_ = crate::leanh::lean_apply_1(v_modifyEnv_1366_, v___x_1370_);
    v___f_1372_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1372_, 0, v_toFunctor_1367_);
    crate::leanh::lean_closure_set(v___f_1372_, 1, v___x_1369_);
    crate::leanh::lean_closure_set(v___f_1372_, 2, v_modifyEnv_1366_);
    crate::leanh::lean_closure_set(v___f_1372_, 3, v_inst_1361_);
    crate::leanh::lean_closure_set(v___f_1372_, 4, v_t_1363_);
    crate::leanh::lean_closure_set(v___f_1372_, 5, v___f_1368_);
    v___f_1373_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1373_, 0, v_inst_1362_);
    crate::leanh::lean_closure_set(v___f_1373_, 1, v_toBind_1365_);
    crate::leanh::lean_closure_set(v___f_1373_, 2, v___f_1372_);
    v___x_1374_ = crate::leanh::lean_apply_4(
        v_toBind_1365_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1371_,
        v___f_1373_,
    );
    return v___x_1374_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical(
    mut v_m_1375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1376_: *mut crate::leanh::LeanObject,
    mut v_inst_1377_: *mut crate::leanh::LeanObject,
    mut v_inst_1378_: *mut crate::leanh::LeanObject,
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_t_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = l_Lean_Elab_Tactic_classical___redArg(
        v_inst_1377_,
        v_inst_1378_,
        v_inst_1379_,
        v_inst_1380_,
        v_t_1381_,
    );
    return v___x_1382_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___x_1384_: *mut crate::leanh::LeanObject,
    mut v___x_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___x_1387_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1423_: u8 = 0;
    let mut v_unused_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_st_ref_take(v___y_1383_);
                v_env_1391_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
                v_nextMacroScope_1392_ = crate::leanh::lean_ctor_get(v___x_1390_, 1);
                v_ngen_1393_ = crate::leanh::lean_ctor_get(v___x_1390_, 2);
                v_auxDeclNGen_1394_ = crate::leanh::lean_ctor_get(v___x_1390_, 3);
                v_traceState_1395_ = crate::leanh::lean_ctor_get(v___x_1390_, 4);
                v_messages_1396_ = crate::leanh::lean_ctor_get(v___x_1390_, 6);
                v_infoState_1397_ = crate::leanh::lean_ctor_get(v___x_1390_, 7);
                v_snapshotTasks_1398_ = crate::leanh::lean_ctor_get(v___x_1390_, 8);
                v_isSharedCheck_1423_ = (!crate::leanh::lean_is_exclusive(v___x_1390_)) as u8;
                if v_isSharedCheck_1423_ == 0 {
                    v_unused_1424_ = crate::leanh::lean_ctor_get(v___x_1390_, 5);
                    crate::leanh::lean_dec(v_unused_1424_);
                    v___x_1400_ = v___x_1390_;
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1398_);
                    crate::leanh::lean_inc(v_infoState_1397_);
                    crate::leanh::lean_inc(v_messages_1396_);
                    crate::leanh::lean_inc(v_traceState_1395_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1394_);
                    crate::leanh::lean_inc(v_ngen_1393_);
                    crate::leanh::lean_inc(v_nextMacroScope_1392_);
                    crate::leanh::lean_inc(v_env_1391_);
                    crate::leanh::lean_dec(v___x_1390_);
                    v___x_1400_ = crate::leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1402_ = l_Lean_ScopedEnvExtension_popScope___redArg(v___x_1384_, v_env_1391_);
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 5, v___x_1385_);
                    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1422_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_nextMacroScope_1392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_ngen_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_auxDeclNGen_1394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_traceState_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 5, v___x_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_messages_1396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_infoState_1397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_snapshotTasks_1398_);
                    v___x_1404_ = v_reuseFailAlloc_1422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1405_ = lean_st_ref_set(v___y_1383_, v___x_1404_);
                v___x_1406_ = lean_st_ref_take(v___y_1386_);
                v_mctx_1407_ = crate::leanh::lean_ctor_get(v___x_1406_, 0);
                v_zetaDeltaFVarIds_1408_ = crate::leanh::lean_ctor_get(v___x_1406_, 2);
                v_postponed_1409_ = crate::leanh::lean_ctor_get(v___x_1406_, 3);
                v_diag_1410_ = crate::leanh::lean_ctor_get(v___x_1406_, 4);
                v_isSharedCheck_1420_ = (!crate::leanh::lean_is_exclusive(v___x_1406_)) as u8;
                if v_isSharedCheck_1420_ == 0 {
                    v_unused_1421_ = crate::leanh::lean_ctor_get(v___x_1406_, 1);
                    crate::leanh::lean_dec(v_unused_1421_);
                    v___x_1412_ = v___x_1406_;
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1410_);
                    crate::leanh::lean_inc(v_postponed_1409_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1408_);
                    crate::leanh::lean_inc(v_mctx_1407_);
                    crate::leanh::lean_dec(v___x_1406_);
                    v___x_1412_ = crate::leanh::lean_box(0);
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1412_, 1, v___x_1387_);
                    v___x_1415_ = v___x_1412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_mctx_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1387_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1419_,
                        2,
                        v_zetaDeltaFVarIds_1408_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_postponed_1409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_diag_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1416_ = lean_st_ref_set(v___y_1386_, v___x_1415_);
                v___x_1417_ = crate::leanh::lean_box(0);
                v___x_1418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___x_1426_: *mut crate::leanh::LeanObject,
    mut v___x_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___x_1429_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1425_, v___x_1426_, v___x_1427_, v___y_1428_, v___x_1429_, v_a_x3f_1430_);
    crate::leanh::lean_dec(v_a_x3f_1430_);
    crate::leanh::lean_dec(v___y_1428_);
    crate::leanh::lean_dec(v___y_1425_);
    return v_res_1432_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1433_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
    v___x_1435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1437_, 0, v___x_1436_);
    crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1436_);
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1439_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 1, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 2, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 3, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 4, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 5, v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
    mut v_t_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_unused_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_a_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_unused_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_reuseFailAlloc_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1522_: u8 = 0;
    let mut v_unused_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1450_ = lean_st_ref_take(v___y_1448_);
                v_env_1451_ = crate::leanh::lean_ctor_get(v___x_1450_, 0);
                v_nextMacroScope_1452_ = crate::leanh::lean_ctor_get(v___x_1450_, 1);
                v_ngen_1453_ = crate::leanh::lean_ctor_get(v___x_1450_, 2);
                v_auxDeclNGen_1454_ = crate::leanh::lean_ctor_get(v___x_1450_, 3);
                v_traceState_1455_ = crate::leanh::lean_ctor_get(v___x_1450_, 4);
                v_messages_1456_ = crate::leanh::lean_ctor_get(v___x_1450_, 6);
                v_infoState_1457_ = crate::leanh::lean_ctor_get(v___x_1450_, 7);
                v_snapshotTasks_1458_ = crate::leanh::lean_ctor_get(v___x_1450_, 8);
                v_isSharedCheck_1525_ = (!crate::leanh::lean_is_exclusive(v___x_1450_)) as u8;
                if v_isSharedCheck_1525_ == 0 {
                    v_unused_1526_ = crate::leanh::lean_ctor_get(v___x_1450_, 5);
                    crate::leanh::lean_dec(v_unused_1526_);
                    v___x_1460_ = v___x_1450_;
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1458_);
                    crate::leanh::lean_inc(v_infoState_1457_);
                    crate::leanh::lean_inc(v_messages_1456_);
                    crate::leanh::lean_inc(v_traceState_1455_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1454_);
                    crate::leanh::lean_inc(v_ngen_1453_);
                    crate::leanh::lean_inc(v_nextMacroScope_1452_);
                    crate::leanh::lean_inc(v_env_1451_);
                    crate::leanh::lean_dec(v___x_1450_);
                    v___x_1460_ = crate::leanh::lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1462_ = l_Lean_Meta_instanceExtension;
                v___x_1463_ =
                    l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_1462_, v_env_1451_);
                v___x_1464_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
                if v_isShared_1461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1460_, 5, v___x_1464_);
                    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1463_);
                    v___x_1466_ = v___x_1460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_traceState_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 5, v___x_1464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_messages_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_infoState_1457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_snapshotTasks_1458_);
                    v___x_1466_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1467_ = lean_st_ref_set(v___y_1448_, v___x_1466_);
                v___x_1468_ = lean_st_ref_take(v___y_1446_);
                v_mctx_1469_ = crate::leanh::lean_ctor_get(v___x_1468_, 0);
                v_zetaDeltaFVarIds_1470_ = crate::leanh::lean_ctor_get(v___x_1468_, 2);
                v_postponed_1471_ = crate::leanh::lean_ctor_get(v___x_1468_, 3);
                v_diag_1472_ = crate::leanh::lean_ctor_get(v___x_1468_, 4);
                v_isSharedCheck_1522_ = (!crate::leanh::lean_is_exclusive(v___x_1468_)) as u8;
                if v_isSharedCheck_1522_ == 0 {
                    v_unused_1523_ = crate::leanh::lean_ctor_get(v___x_1468_, 1);
                    crate::leanh::lean_dec(v_unused_1523_);
                    v___x_1474_ = v___x_1468_;
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1472_);
                    crate::leanh::lean_inc(v_postponed_1471_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1470_);
                    crate::leanh::lean_inc(v_mctx_1469_);
                    crate::leanh::lean_dec(v___x_1468_);
                    v___x_1474_ = crate::leanh::lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
                if v_isShared_1475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1474_, 1, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_mctx_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1476_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1521_,
                        2,
                        v_zetaDeltaFVarIds_1470_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_postponed_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_diag_1472_);
                    v___x_1478_ = v_reuseFailAlloc_1521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1479_ = lean_st_ref_set(v___y_1446_, v___x_1478_);
                v___x_1480_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2;
                v___x_1481_ = 1;
                v___x_1482_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1483_ = l_Lean_Meta_addInstance(
                    v___x_1480_,
                    v___x_1481_,
                    v___x_1482_,
                    v___y_1445_,
                    v___y_1446_,
                    v___y_1447_,
                    v___y_1448_,
                );
                if crate::leanh::lean_obj_tag(v___x_1483_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1483_, 1);
                    crate::leanh::lean_inc(v___y_1448_);
                    crate::leanh::lean_inc_ref(v___y_1447_);
                    crate::leanh::lean_inc(v___y_1446_);
                    crate::leanh::lean_inc_ref(v___y_1445_);
                    crate::leanh::lean_inc(v___y_1444_);
                    crate::leanh::lean_inc_ref(v___y_1443_);
                    crate::leanh::lean_inc(v___y_1442_);
                    crate::leanh::lean_inc_ref(v___y_1441_);
                    v_r_1484_ = crate::leanh::lean_apply_9(
                        v_t_1440_,
                        v___y_1441_,
                        v___y_1442_,
                        v___y_1443_,
                        v___y_1444_,
                        v___y_1445_,
                        v___y_1446_,
                        v___y_1447_,
                        v___y_1448_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_1484_) == 0 {
                        v_a_1485_ = crate::leanh::lean_ctor_get(v_r_1484_, 0);
                        v_isSharedCheck_1501_ = (!crate::leanh::lean_is_exclusive(v_r_1484_)) as u8;
                        if v_isSharedCheck_1501_ == 0 {
                            v___x_1487_ = v_r_1484_;
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1485_);
                            crate::leanh::lean_dec(v_r_1484_);
                            v___x_1487_ = crate::leanh::lean_box(0);
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1502_ = crate::leanh::lean_ctor_get(v_r_1484_, 0);
                        crate::leanh::lean_inc(v_a_1502_);
                        crate::leanh::lean_dec_ref_known(v_r_1484_, 1);
                        v___x_1503_ = crate::leanh::lean_box(0);
                        v___x_1504_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1503_);
                        v_isSharedCheck_1511_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1504_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v_unused_1512_ = crate::leanh::lean_ctor_get(v___x_1504_, 0);
                            crate::leanh::lean_dec(v_unused_1512_);
                            v___x_1506_ = v___x_1504_;
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1504_);
                            v___x_1506_ = crate::leanh::lean_box(0);
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_t_1440_);
                    v_a_1513_ = crate::leanh::lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1520_ = (!crate::leanh::lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1520_ == 0 {
                        v___x_1515_ = v___x_1483_;
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1513_);
                        crate::leanh::lean_dec(v___x_1483_);
                        v___x_1515_ = crate::leanh::lean_box(0);
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_1485_);
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1487_, 1);
                    v___x_1490_ = v___x_1487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1485_);
                    v___x_1490_ = v_reuseFailAlloc_1500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1491_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1490_);
                crate::leanh::lean_dec_ref(v___x_1490_);
                v_isSharedCheck_1498_ = (!crate::leanh::lean_is_exclusive(v___x_1491_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v_unused_1499_ = crate::leanh::lean_ctor_get(v___x_1491_, 0);
                    crate::leanh::lean_dec(v_unused_1499_);
                    v___x_1493_ = v___x_1491_;
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1491_);
                    v___x_1493_ = crate::leanh::lean_box(0);
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1493_, 0, v_a_1485_);
                    v___x_1496_ = v___x_1493_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1485_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1496_;
            }
            9 => {
                if v_isShared_1507_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1506_, 1);
                    crate::leanh::lean_ctor_set(v___x_1506_, 0, v_a_1502_);
                    v___x_1509_ = v___x_1506_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1502_);
                    v___x_1509_ = v_reuseFailAlloc_1510_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1509_;
            }
            11 => {
                if v_isShared_1516_ == 0 {
                    v___x_1518_ = v___x_1515_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
                    v___x_1518_ = v_reuseFailAlloc_1519_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(
    mut v_t_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ =
        l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
            v_t_1527_,
            v___y_1528_,
            v___y_1529_,
            v___y_1530_,
            v___y_1531_,
            v___y_1532_,
            v___y_1533_,
            v___y_1534_,
            v___y_1535_,
        );
    crate::leanh::lean_dec(v___y_1535_);
    crate::leanh::lean_dec_ref(v___y_1534_);
    crate::leanh::lean_dec(v___y_1533_);
    crate::leanh::lean_dec_ref(v___y_1532_);
    crate::leanh::lean_dec(v___y_1531_);
    crate::leanh::lean_dec_ref(v___y_1530_);
    crate::leanh::lean_dec(v___y_1529_);
    crate::leanh::lean_dec_ref(v___y_1528_);
    return v_res_1537_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(
    mut v_00_u03b1_1538_: *mut crate::leanh::LeanObject,
    mut v_t_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v___y_1544_: *mut crate::leanh::LeanObject,
    mut v___y_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ =
        l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
            v_t_1539_,
            v___y_1540_,
            v___y_1541_,
            v___y_1542_,
            v___y_1543_,
            v___y_1544_,
            v___y_1545_,
            v___y_1546_,
            v___y_1547_,
        );
    return v___x_1549_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(
    mut v_00_u03b1_1550_: *mut crate::leanh::LeanObject,
    mut v_t_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(
        v_00_u03b1_1550_,
        v_t_1551_,
        v___y_1552_,
        v___y_1553_,
        v___y_1554_,
        v___y_1555_,
        v___y_1556_,
        v___y_1557_,
        v___y_1558_,
        v___y_1559_,
    );
    crate::leanh::lean_dec(v___y_1559_);
    crate::leanh::lean_dec_ref(v___y_1558_);
    crate::leanh::lean_dec(v___y_1557_);
    crate::leanh::lean_dec_ref(v___y_1556_);
    crate::leanh::lean_dec(v___y_1555_);
    crate::leanh::lean_dec_ref(v___y_1554_);
    crate::leanh::lean_dec(v___y_1553_);
    crate::leanh::lean_dec_ref(v___y_1552_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(
    mut v_stx_1562_: *mut crate::leanh::LeanObject,
    mut v_act_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1584_: u8 = 0;
    let mut v_cancelTk_x3f_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1586_: u8 = 0;
    let mut v_inheritedTraceOptions_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1573_ = crate::leanh::lean_ctor_get(v___y_1570_, 0);
                v_fileMap_1574_ = crate::leanh::lean_ctor_get(v___y_1570_, 1);
                v_options_1575_ = crate::leanh::lean_ctor_get(v___y_1570_, 2);
                v_currRecDepth_1576_ = crate::leanh::lean_ctor_get(v___y_1570_, 3);
                v_maxRecDepth_1577_ = crate::leanh::lean_ctor_get(v___y_1570_, 4);
                v_currNamespace_1578_ = crate::leanh::lean_ctor_get(v___y_1570_, 6);
                v_openDecls_1579_ = crate::leanh::lean_ctor_get(v___y_1570_, 7);
                v_initHeartbeats_1580_ = crate::leanh::lean_ctor_get(v___y_1570_, 8);
                v_maxHeartbeats_1581_ = crate::leanh::lean_ctor_get(v___y_1570_, 9);
                v_quotContext_1582_ = crate::leanh::lean_ctor_get(v___y_1570_, 10);
                v_currMacroScope_1583_ = crate::leanh::lean_ctor_get(v___y_1570_, 11);
                v_diag_1584_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1585_ = crate::leanh::lean_ctor_get(v___y_1570_, 12);
                v_suppressElabErrors_1586_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1587_ = crate::leanh::lean_ctor_get(v___y_1570_, 13);
                if v_suppressElabErrors_1586_ == 0 {
                    v___y_1589_ = v_suppressElabErrors_1586_;
                    state = 1;
                    continue;
                } else {
                    v___x_1592_ = l_Lean_Syntax_hasMissing(v_stx_1562_);
                    v___y_1589_ = v___x_1592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1587_);
                crate::leanh::lean_inc(v_cancelTk_x3f_1585_);
                crate::leanh::lean_inc(v_currMacroScope_1583_);
                crate::leanh::lean_inc(v_quotContext_1582_);
                crate::leanh::lean_inc(v_maxHeartbeats_1581_);
                crate::leanh::lean_inc(v_initHeartbeats_1580_);
                crate::leanh::lean_inc(v_openDecls_1579_);
                crate::leanh::lean_inc(v_currNamespace_1578_);
                crate::leanh::lean_inc(v_maxRecDepth_1577_);
                crate::leanh::lean_inc(v_currRecDepth_1576_);
                crate::leanh::lean_inc_ref(v_options_1575_);
                crate::leanh::lean_inc_ref(v_fileMap_1574_);
                crate::leanh::lean_inc_ref(v_fileName_1573_);
                v___x_1590_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1590_, 0, v_fileName_1573_);
                crate::leanh::lean_ctor_set(v___x_1590_, 1, v_fileMap_1574_);
                crate::leanh::lean_ctor_set(v___x_1590_, 2, v_options_1575_);
                crate::leanh::lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1576_);
                crate::leanh::lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1577_);
                crate::leanh::lean_ctor_set(v___x_1590_, 5, v_stx_1562_);
                crate::leanh::lean_ctor_set(v___x_1590_, 6, v_currNamespace_1578_);
                crate::leanh::lean_ctor_set(v___x_1590_, 7, v_openDecls_1579_);
                crate::leanh::lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1580_);
                crate::leanh::lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1581_);
                crate::leanh::lean_ctor_set(v___x_1590_, 10, v_quotContext_1582_);
                crate::leanh::lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1583_);
                crate::leanh::lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1585_);
                crate::leanh::lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1587_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1584_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1589_,
                );
                crate::leanh::lean_inc(v___y_1571_);
                crate::leanh::lean_inc(v___y_1569_);
                crate::leanh::lean_inc_ref(v___y_1568_);
                crate::leanh::lean_inc(v___y_1567_);
                crate::leanh::lean_inc_ref(v___y_1566_);
                crate::leanh::lean_inc(v___y_1565_);
                crate::leanh::lean_inc_ref(v___y_1564_);
                v___x_1591_ = crate::leanh::lean_apply_9(
                    v_act_1563_,
                    v___y_1564_,
                    v___y_1565_,
                    v___y_1566_,
                    v___y_1567_,
                    v___y_1568_,
                    v___y_1569_,
                    v___x_1590_,
                    v___y_1571_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_stx_1593_: *mut crate::leanh::LeanObject,
    mut v_act_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1593_, v_act_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
    crate::leanh::lean_dec(v___y_1602_);
    crate::leanh::lean_dec_ref(v___y_1601_);
    crate::leanh::lean_dec(v___y_1600_);
    crate::leanh::lean_dec_ref(v___y_1599_);
    crate::leanh::lean_dec(v___y_1598_);
    crate::leanh::lean_dec_ref(v___y_1597_);
    crate::leanh::lean_dec(v___y_1596_);
    crate::leanh::lean_dec_ref(v___y_1595_);
    return v_res_1604_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(
    mut v_act_1605_: *mut crate::leanh::LeanObject,
    mut v_snd_1606_: *mut crate::leanh::LeanObject,
    mut v_____r_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_snd_1606_);
    v___x_1617_ = crate::leanh::lean_apply_1(v_act_1605_, v_snd_1606_);
    v___x_1618_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_1606_, v___x_1617_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_act_1619_: *mut crate::leanh::LeanObject,
    mut v_snd_1620_: *mut crate::leanh::LeanObject,
    mut v_____r_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_1619_, v_snd_1620_, v_____r_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
    crate::leanh::lean_dec(v___y_1629_);
    crate::leanh::lean_dec_ref(v___y_1628_);
    crate::leanh::lean_dec(v___y_1627_);
    crate::leanh::lean_dec_ref(v___y_1626_);
    crate::leanh::lean_dec(v___y_1625_);
    crate::leanh::lean_dec_ref(v___y_1624_);
    crate::leanh::lean_dec(v___y_1623_);
    crate::leanh::lean_dec_ref(v___y_1622_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(
    mut v_val_1633_: *mut crate::leanh::LeanObject,
    mut v___f_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tacSnap_x3f_1649_ = crate::leanh::lean_ctor_get(v___y_1637_, 6);
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_1649_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_1650_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_1649_, 0);
                    v_old_x3f_1651_ = crate::leanh::lean_ctor_get(v_val_1650_, 0);
                    if crate::leanh::lean_obj_tag(v_old_x3f_1651_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_val_1633_);
                        v___x_1652_ = crate::leanh::lean_box(0);
                        v___x_1653_ = crate::leanh::lean_apply_10(
                            v___f_1634_,
                            v___x_1652_,
                            v___y_1635_,
                            v___y_1636_,
                            v___y_1637_,
                            v___y_1638_,
                            v___y_1639_,
                            v___y_1640_,
                            v___y_1641_,
                            v___y_1642_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_1653_;
                    }
                }
            }
            1 => {
                v_val_1645_ = crate::leanh::lean_ctor_get(v_val_1633_, 1);
                crate::leanh::lean_inc(v_val_1645_);
                crate::leanh::lean_dec_ref(v_val_1633_);
                v___x_1646_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0;
                v___x_1647_ =
                    l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_1646_, v_val_1645_);
                v___x_1648_ = crate::leanh::lean_apply_10(
                    v___f_1634_,
                    v___x_1647_,
                    v___y_1635_,
                    v___y_1636_,
                    v___y_1637_,
                    v___y_1638_,
                    v___y_1639_,
                    v___y_1640_,
                    v___y_1641_,
                    v___y_1642_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(
    mut v_val_1654_: *mut crate::leanh::LeanObject,
    mut v___f_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_1654_, v___f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(
    mut v_split_1666_: *mut crate::leanh::LeanObject,
    mut v_act_1667_: *mut crate::leanh::LeanObject,
    mut v_stx_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1679_: u8 = 0;
    let mut v___y_1680_: u8 = 0;
    let mut v___y_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: u8 = 0;
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: u8 = 0;
    let mut v___y_1688_: u8 = 0;
    let mut v___y_1689_: u8 = 0;
    let mut v___y_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: u8 = 0;
    let mut v___y_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: u8 = 0;
    let mut v___y_1694_: u8 = 0;
    let mut v___y_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: u8 = 0;
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: u8 = 0;
    let mut v___y_1703_: u8 = 0;
    let mut v___y_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: u8 = 0;
    let mut v___y_1707_: u8 = 0;
    let mut v___y_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: u8 = 0;
    let mut v___y_1712_: u8 = 0;
    let mut v___y_1713_: u8 = 0;
    let mut v___y_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: u8 = 0;
    let mut v___y_1716_: u8 = 0;
    let mut v___y_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: u8 = 0;
    let mut v___y_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: u8 = 0;
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_1731_: u8 = 0;
    let mut v_errToSorry_1732_: u8 = 0;
    let mut v_autoBoundImplicitContext_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_1734_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_1737_: u8 = 0;
    let mut v_heedElabAsElim_1738_: u8 = 0;
    let mut v_isNoncomputableSection_1739_: u8 = 0;
    let mut v_isMetaSection_1740_: u8 = 0;
    let mut v_ignoreTCFailures_1741_: u8 = 0;
    let mut v_inPattern_1742_: u8 = 0;
    let mut v_tacSnap_x3f_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_1744_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_1745_: u8 = 0;
    let mut v_checkDeprecated_1746_: u8 = 0;
    let mut v_fixedTermElabs_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v___f_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_split_1666_);
                v___x_1725_ = crate::leanh::lean_apply_1(v_split_1666_, v_stx_1668_);
                v_fst_1726_ = crate::leanh::lean_ctor_get(v___x_1725_, 0);
                crate::leanh::lean_inc(v_fst_1726_);
                v_snd_1727_ = crate::leanh::lean_ctor_get(v___x_1725_, 1);
                crate::leanh::lean_inc_n(v_snd_1727_, 2);
                crate::leanh::lean_dec_ref(v___x_1725_);
                v_options_1728_ = crate::leanh::lean_ctor_get(v___y_1675_, 2);
                v_declName_x3f_1729_ = crate::leanh::lean_ctor_get(v___y_1671_, 0);
                v_macroStack_1730_ = crate::leanh::lean_ctor_get(v___y_1671_, 1);
                v_mayPostpone_1731_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_1732_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_1733_ = crate::leanh::lean_ctor_get(v___y_1671_, 2);
                v_autoBoundImplicitForbidden_1734_ = crate::leanh::lean_ctor_get(v___y_1671_, 3);
                v_sectionVars_1735_ = crate::leanh::lean_ctor_get(v___y_1671_, 4);
                v_sectionFVars_1736_ = crate::leanh::lean_ctor_get(v___y_1671_, 5);
                v_implicitLambda_1737_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_1738_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_1739_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_1740_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_1741_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_1742_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_1743_ = crate::leanh::lean_ctor_get(v___y_1671_, 6);
                v_saveRecAppSyntax_1744_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_1745_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_1746_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_1747_ = crate::leanh::lean_ctor_get(v___y_1671_, 7);
                crate::leanh::lean_inc_ref(v_act_1667_);
                v___f_1770_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 2);
                crate::leanh::lean_closure_set(v___f_1770_, 0, v_act_1667_);
                crate::leanh::lean_closure_set(v___f_1770_, 1, v_snd_1727_);
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1770_);
                    state = 6;
                    continue;
                } else {
                    v_val_1774_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1775_ = crate::leanh::lean_ctor_get(v_val_1774_, 0);
                    if crate::leanh::lean_obj_tag(v_old_x3f_1775_) == 1 {
                        crate::leanh::lean_dec(v_snd_1727_);
                        crate::leanh::lean_dec_ref(v_act_1667_);
                        v_val_1776_ = crate::leanh::lean_ctor_get(v_old_x3f_1775_, 0);
                        crate::leanh::lean_inc(v_val_1776_);
                        v___f_1777_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
                        crate::leanh::lean_closure_set(v___f_1777_, 0, v_val_1776_);
                        crate::leanh::lean_closure_set(v___f_1777_, 1, v___f_1770_);
                        v___y_1749_ = v___f_1777_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_1770_);
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1695_);
                crate::leanh::lean_inc(v___y_1690_);
                crate::leanh::lean_inc(v___y_1682_);
                crate::leanh::lean_inc_ref(v___y_1686_);
                crate::leanh::lean_inc(v___y_1681_);
                crate::leanh::lean_inc(v___y_1685_);
                crate::leanh::lean_inc(v___y_1696_);
                v___x_1699_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                crate::leanh::lean_ctor_set(v___x_1699_, 0, v___y_1696_);
                crate::leanh::lean_ctor_set(v___x_1699_, 1, v___y_1685_);
                crate::leanh::lean_ctor_set(v___x_1699_, 2, v___y_1681_);
                crate::leanh::lean_ctor_set(v___x_1699_, 3, v___y_1686_);
                crate::leanh::lean_ctor_set(v___x_1699_, 4, v___y_1682_);
                crate::leanh::lean_ctor_set(v___x_1699_, 5, v___y_1690_);
                crate::leanh::lean_ctor_set(v___x_1699_, 6, v___y_1698_);
                crate::leanh::lean_ctor_set(v___x_1699_, 7, v___y_1695_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v___y_1680_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v___y_1687_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    v___y_1697_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    v___y_1684_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                    v___y_1688_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                    v___y_1694_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                    v___y_1691_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                    v___y_1679_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                    v___y_1693_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                    v___y_1683_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                    v___y_1689_,
                );
                crate::leanh::lean_inc(v___y_1676_);
                crate::leanh::lean_inc_ref(v___y_1675_);
                crate::leanh::lean_inc(v___y_1674_);
                crate::leanh::lean_inc_ref(v___y_1673_);
                crate::leanh::lean_inc(v___y_1672_);
                crate::leanh::lean_inc(v___y_1670_);
                crate::leanh::lean_inc_ref(v___y_1669_);
                v___x_1700_ = crate::leanh::lean_apply_9(
                    v___y_1692_,
                    v___y_1669_,
                    v___y_1670_,
                    v___x_1699_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                    v___y_1675_,
                    v___y_1676_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1700_;
            }
            2 => {
                v___x_1723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1723_, 0, v___y_1722_);
                crate::leanh::lean_ctor_set(v___x_1723_, 1, v_new_1709_);
                v___x_1724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1724_, 0, v___x_1723_);
                v___y_1679_ = v___y_1702_;
                v___y_1680_ = v___y_1703_;
                v___y_1681_ = v___y_1704_;
                v___y_1682_ = v___y_1705_;
                v___y_1683_ = v___y_1706_;
                v___y_1684_ = v___y_1707_;
                v___y_1685_ = v___y_1708_;
                v___y_1686_ = v___y_1710_;
                v___y_1687_ = v___y_1711_;
                v___y_1688_ = v___y_1712_;
                v___y_1689_ = v___y_1713_;
                v___y_1690_ = v___y_1714_;
                v___y_1691_ = v___y_1715_;
                v___y_1692_ = v___y_1717_;
                v___y_1693_ = v___y_1716_;
                v___y_1694_ = v___y_1718_;
                v___y_1695_ = v___y_1719_;
                v___y_1696_ = v___y_1720_;
                v___y_1697_ = v___y_1721_;
                v___y_1698_ = v___x_1724_;
                state = 1;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    crate::leanh::lean_dec(v_fst_1726_);
                    crate::leanh::lean_dec_ref(v_split_1666_);
                    v___y_1679_ = v_inPattern_1742_;
                    v___y_1680_ = v_mayPostpone_1731_;
                    v___y_1681_ = v_autoBoundImplicitContext_1733_;
                    v___y_1682_ = v_sectionVars_1735_;
                    v___y_1683_ = v_holesAsSyntheticOpaque_1745_;
                    v___y_1684_ = v_heedElabAsElim_1738_;
                    v___y_1685_ = v_macroStack_1730_;
                    v___y_1686_ = v_autoBoundImplicitForbidden_1734_;
                    v___y_1687_ = v_errToSorry_1732_;
                    v___y_1688_ = v_isNoncomputableSection_1739_;
                    v___y_1689_ = v_checkDeprecated_1746_;
                    v___y_1690_ = v_sectionFVars_1736_;
                    v___y_1691_ = v_ignoreTCFailures_1741_;
                    v___y_1692_ = v___y_1749_;
                    v___y_1693_ = v_saveRecAppSyntax_1744_;
                    v___y_1694_ = v_isMetaSection_1740_;
                    v___y_1695_ = v_fixedTermElabs_1747_;
                    v___y_1696_ = v_declName_x3f_1729_;
                    v___y_1697_ = v_implicitLambda_1737_;
                    v___y_1698_ = v_tacSnap_x3f_1743_;
                    state = 1;
                    continue;
                } else {
                    v_val_1750_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1751_ = crate::leanh::lean_ctor_get(v_val_1750_, 0);
                    if crate::leanh::lean_obj_tag(v_old_x3f_1751_) == 0 {
                        crate::leanh::lean_dec(v_fst_1726_);
                        crate::leanh::lean_dec_ref(v_split_1666_);
                        v_new_1752_ = crate::leanh::lean_ctor_get(v_val_1750_, 1);
                        crate::leanh::lean_inc(v_new_1752_);
                        v___y_1702_ = v_inPattern_1742_;
                        v___y_1703_ = v_mayPostpone_1731_;
                        v___y_1704_ = v_autoBoundImplicitContext_1733_;
                        v___y_1705_ = v_sectionVars_1735_;
                        v___y_1706_ = v_holesAsSyntheticOpaque_1745_;
                        v___y_1707_ = v_heedElabAsElim_1738_;
                        v___y_1708_ = v_macroStack_1730_;
                        v_new_1709_ = v_new_1752_;
                        v___y_1710_ = v_autoBoundImplicitForbidden_1734_;
                        v___y_1711_ = v_errToSorry_1732_;
                        v___y_1712_ = v_isNoncomputableSection_1739_;
                        v___y_1713_ = v_checkDeprecated_1746_;
                        v___y_1714_ = v_sectionFVars_1736_;
                        v___y_1715_ = v_ignoreTCFailures_1741_;
                        v___y_1716_ = v_saveRecAppSyntax_1744_;
                        v___y_1717_ = v___y_1749_;
                        v___y_1718_ = v_isMetaSection_1740_;
                        v___y_1719_ = v_fixedTermElabs_1747_;
                        v___y_1720_ = v_declName_x3f_1729_;
                        v___y_1721_ = v_implicitLambda_1737_;
                        v___y_1722_ = v_old_x3f_1751_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1753_ = crate::leanh::lean_ctor_get(v_old_x3f_1751_, 0);
                        v_new_1754_ = crate::leanh::lean_ctor_get(v_val_1750_, 1);
                        v_stx_1755_ = crate::leanh::lean_ctor_get(v_val_1753_, 0);
                        v_val_1756_ = crate::leanh::lean_ctor_get(v_val_1753_, 1);
                        crate::leanh::lean_inc(v_stx_1755_);
                        v___x_1757_ = crate::leanh::lean_apply_1(v_split_1666_, v_stx_1755_);
                        v_fst_1758_ = crate::leanh::lean_ctor_get(v___x_1757_, 0);
                        v_snd_1759_ = crate::leanh::lean_ctor_get(v___x_1757_, 1);
                        v_isSharedCheck_1769_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1757_)) as u8;
                        if v_isSharedCheck_1769_ == 0 {
                            v___x_1761_ = v___x_1757_;
                            v_isShared_1762_ = v_isSharedCheck_1769_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1759_);
                            crate::leanh::lean_inc(v_fst_1758_);
                            crate::leanh::lean_dec(v___x_1757_);
                            v___x_1761_ = crate::leanh::lean_box(0);
                            v_isShared_1762_ = v_isSharedCheck_1769_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1763_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(
                    v_options_1728_,
                    v_fst_1726_,
                    v_fst_1758_,
                );
                if v___x_1763_ == 0 {
                    crate::leanh::lean_del_object(v___x_1761_);
                    crate::leanh::lean_dec(v_snd_1759_);
                    v___x_1764_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_new_1754_);
                    v___y_1702_ = v_inPattern_1742_;
                    v___y_1703_ = v_mayPostpone_1731_;
                    v___y_1704_ = v_autoBoundImplicitContext_1733_;
                    v___y_1705_ = v_sectionVars_1735_;
                    v___y_1706_ = v_holesAsSyntheticOpaque_1745_;
                    v___y_1707_ = v_heedElabAsElim_1738_;
                    v___y_1708_ = v_macroStack_1730_;
                    v_new_1709_ = v_new_1754_;
                    v___y_1710_ = v_autoBoundImplicitForbidden_1734_;
                    v___y_1711_ = v_errToSorry_1732_;
                    v___y_1712_ = v_isNoncomputableSection_1739_;
                    v___y_1713_ = v_checkDeprecated_1746_;
                    v___y_1714_ = v_sectionFVars_1736_;
                    v___y_1715_ = v_ignoreTCFailures_1741_;
                    v___y_1716_ = v_saveRecAppSyntax_1744_;
                    v___y_1717_ = v___y_1749_;
                    v___y_1718_ = v_isMetaSection_1740_;
                    v___y_1719_ = v_fixedTermElabs_1747_;
                    v___y_1720_ = v_declName_x3f_1729_;
                    v___y_1721_ = v_implicitLambda_1737_;
                    v___y_1722_ = v___x_1764_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1756_);
                    if v_isShared_1762_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1761_, 1, v_val_1756_);
                        crate::leanh::lean_ctor_set(v___x_1761_, 0, v_snd_1759_);
                        v___x_1766_ = v___x_1761_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_snd_1759_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_val_1756_);
                        v___x_1766_ = v_reuseFailAlloc_1768_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
                crate::leanh::lean_inc(v_new_1754_);
                v___y_1702_ = v_inPattern_1742_;
                v___y_1703_ = v_mayPostpone_1731_;
                v___y_1704_ = v_autoBoundImplicitContext_1733_;
                v___y_1705_ = v_sectionVars_1735_;
                v___y_1706_ = v_holesAsSyntheticOpaque_1745_;
                v___y_1707_ = v_heedElabAsElim_1738_;
                v___y_1708_ = v_macroStack_1730_;
                v_new_1709_ = v_new_1754_;
                v___y_1710_ = v_autoBoundImplicitForbidden_1734_;
                v___y_1711_ = v_errToSorry_1732_;
                v___y_1712_ = v_isNoncomputableSection_1739_;
                v___y_1713_ = v_checkDeprecated_1746_;
                v___y_1714_ = v_sectionFVars_1736_;
                v___y_1715_ = v_ignoreTCFailures_1741_;
                v___y_1716_ = v_saveRecAppSyntax_1744_;
                v___y_1717_ = v___y_1749_;
                v___y_1718_ = v_isMetaSection_1740_;
                v___y_1719_ = v_fixedTermElabs_1747_;
                v___y_1720_ = v_declName_x3f_1729_;
                v___y_1721_ = v_implicitLambda_1737_;
                v___y_1722_ = v___x_1767_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1772_ = crate::leanh::lean_box(0);
                v___x_1773_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 3);
                crate::leanh::lean_closure_set(v___x_1773_, 0, v_act_1667_);
                crate::leanh::lean_closure_set(v___x_1773_, 1, v_snd_1727_);
                crate::leanh::lean_closure_set(v___x_1773_, 2, v___x_1772_);
                v___y_1749_ = v___x_1773_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(
    mut v_split_1778_: *mut crate::leanh::LeanObject,
    mut v_act_1779_: *mut crate::leanh::LeanObject,
    mut v_stx_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1790_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1778_, v_act_1779_, v_stx_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
    crate::leanh::lean_dec(v___y_1788_);
    crate::leanh::lean_dec_ref(v___y_1787_);
    crate::leanh::lean_dec(v___y_1786_);
    crate::leanh::lean_dec_ref(v___y_1785_);
    crate::leanh::lean_dec(v___y_1784_);
    crate::leanh::lean_dec_ref(v___y_1783_);
    crate::leanh::lean_dec(v___y_1782_);
    crate::leanh::lean_dec_ref(v___y_1781_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(
    mut v_argIdx_1794_: *mut crate::leanh::LeanObject,
    mut v_stx_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Syntax_getArgs(v_stx_1795_);
    v___x_1797_ = crate::leanh::lean_unsigned_to_nat(0);
    crate::leanh::lean_inc(v_argIdx_1794_);
    v___x_1798_ = l_Array_toSubarray___redArg(v___x_1796_, v___x_1797_, v_argIdx_1794_);
    v___x_1799_ = l_Subarray_copy___redArg(v___x_1798_);
    v___x_1800_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1;
    v___x_1801_ = crate::leanh::lean_box(2);
    v___x_1802_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    crate::leanh::lean_ctor_set(v___x_1802_, 1, v___x_1800_);
    crate::leanh::lean_ctor_set(v___x_1802_, 2, v___x_1799_);
    v___x_1803_ = l_Lean_Syntax_getArg(v_stx_1795_, v_argIdx_1794_);
    crate::leanh::lean_dec(v_argIdx_1794_);
    v___x_1804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(
    mut v_argIdx_1805_: *mut crate::leanh::LeanObject,
    mut v_stx_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_1805_, v_stx_1806_);
    crate::leanh::lean_dec(v_stx_1806_);
    return v_res_1807_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(
    mut v_argIdx_1808_: *mut crate::leanh::LeanObject,
    mut v_act_1809_: *mut crate::leanh::LeanObject,
    mut v_stx_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1820_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_1820_, 0, v_argIdx_1808_);
    v___x_1821_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_1820_, v_act_1809_, v_stx_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(
    mut v_argIdx_1822_: *mut crate::leanh::LeanObject,
    mut v_act_1823_: *mut crate::leanh::LeanObject,
    mut v_stx_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1822_, v_act_1823_, v_stx_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    crate::leanh::lean_dec(v___y_1832_);
    crate::leanh::lean_dec_ref(v___y_1831_);
    crate::leanh::lean_dec(v___y_1830_);
    crate::leanh::lean_dec_ref(v___y_1829_);
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    crate::leanh::lean_dec(v___y_1826_);
    crate::leanh::lean_dec_ref(v___y_1825_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(
    mut v_00_u03b1_1835_: *mut crate::leanh::LeanObject,
    mut v_argIdx_1836_: *mut crate::leanh::LeanObject,
    mut v_act_1837_: *mut crate::leanh::LeanObject,
    mut v_stx_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1836_, v_act_1837_, v_stx_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    return v___x_1848_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(
    mut v_00_u03b1_1849_: *mut crate::leanh::LeanObject,
    mut v_argIdx_1850_: *mut crate::leanh::LeanObject,
    mut v_act_1851_: *mut crate::leanh::LeanObject,
    mut v_stx_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ =
        l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(
            v_00_u03b1_1849_,
            v_argIdx_1850_,
            v_act_1851_,
            v_stx_1852_,
            v___y_1853_,
            v___y_1854_,
            v___y_1855_,
            v___y_1856_,
            v___y_1857_,
            v___y_1858_,
            v___y_1859_,
            v___y_1860_,
        );
    crate::leanh::lean_dec(v___y_1860_);
    crate::leanh::lean_dec_ref(v___y_1859_);
    crate::leanh::lean_dec(v___y_1858_);
    crate::leanh::lean_dec_ref(v___y_1857_);
    crate::leanh::lean_dec(v___y_1856_);
    crate::leanh::lean_dec_ref(v___y_1855_);
    crate::leanh::lean_dec(v___y_1854_);
    crate::leanh::lean_dec_ref(v___y_1853_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = lean_st_ref_get(v___y_1865_);
    v_env_1868_ = crate::leanh::lean_ctor_get(v___x_1867_, 0);
    crate::leanh::lean_inc_ref(v_env_1868_);
    crate::leanh::lean_dec(v___x_1867_);
    v___x_1869_ = lean_st_ref_get(v___y_1863_);
    v_mctx_1870_ = crate::leanh::lean_ctor_get(v___x_1869_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1870_);
    crate::leanh::lean_dec(v___x_1869_);
    v_options_1871_ = crate::leanh::lean_ctor_get(v___y_1864_, 2);
    v_currNamespace_1872_ = crate::leanh::lean_ctor_get(v___y_1864_, 6);
    v_openDecls_1873_ = crate::leanh::lean_ctor_get(v___y_1864_, 7);
    v___x_1874_ = lean_st_ref_get(v___y_1865_);
    v_ngen_1875_ = crate::leanh::lean_ctor_get(v___x_1874_, 2);
    crate::leanh::lean_inc_ref(v_ngen_1875_);
    crate::leanh::lean_dec(v___x_1874_);
    v___x_1876_ = crate::leanh::lean_box(0);
    v___x_1877_ = l_Lean_instInhabitedFileMap_default;
    crate::leanh::lean_inc(v_openDecls_1873_);
    crate::leanh::lean_inc(v_currNamespace_1872_);
    crate::leanh::lean_inc_ref(v_options_1871_);
    v___x_1878_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1878_, 0, v_env_1868_);
    crate::leanh::lean_ctor_set(v___x_1878_, 1, v___x_1876_);
    crate::leanh::lean_ctor_set(v___x_1878_, 2, v___x_1877_);
    crate::leanh::lean_ctor_set(v___x_1878_, 3, v_mctx_1870_);
    crate::leanh::lean_ctor_set(v___x_1878_, 4, v_options_1871_);
    crate::leanh::lean_ctor_set(v___x_1878_, 5, v_currNamespace_1872_);
    crate::leanh::lean_ctor_set(v___x_1878_, 6, v_openDecls_1873_);
    crate::leanh::lean_ctor_set(v___x_1878_, 7, v_ngen_1875_);
    v___x_1879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1880_, v___y_1881_, v___y_1882_);
    crate::leanh::lean_dec(v___y_1882_);
    crate::leanh::lean_dec_ref(v___y_1881_);
    crate::leanh::lean_dec(v___y_1880_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1894_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1890_, v___y_1891_, v___y_1892_);
                v_a_1895_ = crate::leanh::lean_ctor_get(v___x_1894_, 0);
                v_isSharedCheck_1919_ = (!crate::leanh::lean_is_exclusive(v___x_1894_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1897_ = v___x_1894_;
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1895_);
                    crate::leanh::lean_dec(v___x_1894_);
                    v___x_1897_ = crate::leanh::lean_box(0);
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1899_ = crate::leanh::lean_ctor_get(v___y_1891_, 1);
                v_env_1900_ = crate::leanh::lean_ctor_get(v_a_1895_, 0);
                v_mctx_1901_ = crate::leanh::lean_ctor_get(v_a_1895_, 3);
                v_options_1902_ = crate::leanh::lean_ctor_get(v_a_1895_, 4);
                v_currNamespace_1903_ = crate::leanh::lean_ctor_get(v_a_1895_, 5);
                v_openDecls_1904_ = crate::leanh::lean_ctor_get(v_a_1895_, 6);
                v_ngen_1905_ = crate::leanh::lean_ctor_get(v_a_1895_, 7);
                v_isSharedCheck_1916_ = (!crate::leanh::lean_is_exclusive(v_a_1895_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v_unused_1917_ = crate::leanh::lean_ctor_get(v_a_1895_, 2);
                    crate::leanh::lean_dec(v_unused_1917_);
                    v_unused_1918_ = crate::leanh::lean_ctor_get(v_a_1895_, 1);
                    crate::leanh::lean_dec(v_unused_1918_);
                    v___x_1907_ = v_a_1895_;
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_1905_);
                    crate::leanh::lean_inc(v_openDecls_1904_);
                    crate::leanh::lean_inc(v_currNamespace_1903_);
                    crate::leanh::lean_inc(v_options_1902_);
                    crate::leanh::lean_inc(v_mctx_1901_);
                    crate::leanh::lean_inc(v_env_1900_);
                    crate::leanh::lean_dec(v_a_1895_);
                    v___x_1907_ = crate::leanh::lean_box(0);
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1909_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_fileMap_1899_);
                if v_isShared_1908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1907_, 2, v_fileMap_1899_);
                    crate::leanh::lean_ctor_set(v___x_1907_, 1, v___x_1909_);
                    v___x_1911_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_env_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_fileMap_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_mctx_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_options_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_currNamespace_1903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_openDecls_1904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_ngen_1905_);
                    v___x_1911_ = v_reuseFailAlloc_1915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec(v___y_1925_);
    crate::leanh::lean_dec_ref(v___y_1924_);
    crate::leanh::lean_dec(v___y_1923_);
    crate::leanh::lean_dec_ref(v___y_1922_);
    crate::leanh::lean_dec(v___y_1921_);
    crate::leanh::lean_dec_ref(v___y_1920_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1939_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
                v_a_1940_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                v_isSharedCheck_1949_ = (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                if v_isSharedCheck_1949_ == 0 {
                    v___x_1942_ = v___x_1939_;
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1940_);
                    crate::leanh::lean_dec(v___x_1939_);
                    v___x_1942_ = crate::leanh::lean_box(0);
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1944_, 0, v_a_1940_);
                v___x_1945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1945_, 0, v___x_1944_);
                if v_isShared_1943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1945_);
                    v___x_1947_ = v___x_1942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
                    v___x_1947_ = v_reuseFailAlloc_1948_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
    crate::leanh::lean_dec(v___y_1957_);
    crate::leanh::lean_dec_ref(v___y_1956_);
    crate::leanh::lean_dec(v___y_1955_);
    crate::leanh::lean_dec_ref(v___y_1954_);
    crate::leanh::lean_dec(v___y_1953_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    crate::leanh::lean_dec(v___y_1951_);
    crate::leanh::lean_dec_ref(v___y_1950_);
    return v_res_1959_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
    v___x_1962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = 5usize;
    v___x_1964_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1965_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
    v___x_1967_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
    v___x_1968_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    crate::leanh::lean_ctor_set(v___x_1968_, 1, v___x_1966_);
    crate::leanh::lean_ctor_set(v___x_1968_, 2, v___x_1964_);
    crate::leanh::lean_ctor_set(v___x_1968_, 3, v___x_1964_);
    crate::leanh::lean_ctor_set_usize(v___x_1968_, 4, v___x_1963_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(
    mut v___y_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v_enabled_1987_: u8 = 0;
    let mut v_assignment_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1971_ = lean_st_ref_get(v___y_1969_);
                v_infoState_1972_ = crate::leanh::lean_ctor_get(v___x_1971_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1972_);
                crate::leanh::lean_dec(v___x_1971_);
                v_trees_1973_ = crate::leanh::lean_ctor_get(v_infoState_1972_, 2);
                crate::leanh::lean_inc_ref(v_trees_1973_);
                crate::leanh::lean_dec_ref(v_infoState_1972_);
                v___x_1974_ = lean_st_ref_take(v___y_1969_);
                v_infoState_1975_ = crate::leanh::lean_ctor_get(v___x_1974_, 7);
                v_env_1976_ = crate::leanh::lean_ctor_get(v___x_1974_, 0);
                v_nextMacroScope_1977_ = crate::leanh::lean_ctor_get(v___x_1974_, 1);
                v_ngen_1978_ = crate::leanh::lean_ctor_get(v___x_1974_, 2);
                v_auxDeclNGen_1979_ = crate::leanh::lean_ctor_get(v___x_1974_, 3);
                v_traceState_1980_ = crate::leanh::lean_ctor_get(v___x_1974_, 4);
                v_cache_1981_ = crate::leanh::lean_ctor_get(v___x_1974_, 5);
                v_messages_1982_ = crate::leanh::lean_ctor_get(v___x_1974_, 6);
                v_snapshotTasks_1983_ = crate::leanh::lean_ctor_get(v___x_1974_, 8);
                v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1985_ = v___x_1974_;
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1983_);
                    crate::leanh::lean_inc(v_infoState_1975_);
                    crate::leanh::lean_inc(v_messages_1982_);
                    crate::leanh::lean_inc(v_cache_1981_);
                    crate::leanh::lean_inc(v_traceState_1980_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1979_);
                    crate::leanh::lean_inc(v_ngen_1978_);
                    crate::leanh::lean_inc(v_nextMacroScope_1977_);
                    crate::leanh::lean_inc(v_env_1976_);
                    crate::leanh::lean_dec(v___x_1974_);
                    v___x_1985_ = crate::leanh::lean_box(0);
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1987_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1975_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1988_ = crate::leanh::lean_ctor_get(v_infoState_1975_, 0);
                v_lazyAssignment_1989_ = crate::leanh::lean_ctor_get(v_infoState_1975_, 1);
                v_isSharedCheck_2002_ = (!crate::leanh::lean_is_exclusive(v_infoState_1975_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = crate::leanh::lean_ctor_get(v_infoState_1975_, 2);
                    crate::leanh::lean_dec(v_unused_2003_);
                    v___x_1991_ = v_infoState_1975_;
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1989_);
                    crate::leanh::lean_inc(v_assignment_1988_);
                    crate::leanh::lean_dec(v_infoState_1975_);
                    v___x_1991_ = crate::leanh::lean_box(0);
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
                if v_isShared_1992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1991_, 2, v___x_1993_);
                    v___x_1995_ = v___x_1991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_assignment_1988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_lazyAssignment_1989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 2, v___x_1993_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2001_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1987_,
                    );
                    v___x_1995_ = v_reuseFailAlloc_2001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1985_, 7, v___x_1995_);
                    v___x_1997_ = v___x_1985_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_env_1976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_nextMacroScope_1977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_ngen_1978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_auxDeclNGen_1979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_traceState_1980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 5, v_cache_1981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 6, v_messages_1982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 7, v___x_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 8, v_snapshotTasks_1983_);
                    v___x_1997_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1998_ = lean_st_ref_set(v___y_1969_, v___x_1997_);
                v___x_1999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1999_, 0, v_trees_1973_);
                return v___x_1999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2005_);
    crate::leanh::lean_dec(v___y_2005_);
    return v_res_2007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(
    mut v___x_2008_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2009_: *mut crate::leanh::LeanObject,
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_bs_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
    mut v___y_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: usize = 0;
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2022_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2022_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2009_);
                    v___x_2023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2023_, 0, v_bs_2012_);
                    return v___x_2023_;
                } else {
                    v_assignment_2024_ = crate::leanh::lean_ctor_get(v___x_2008_, 0);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_2009_);
                    crate::leanh::lean_inc(v___y_2020_);
                    crate::leanh::lean_inc_ref(v___y_2019_);
                    crate::leanh::lean_inc(v___y_2018_);
                    crate::leanh::lean_inc_ref(v___y_2017_);
                    crate::leanh::lean_inc(v___y_2016_);
                    crate::leanh::lean_inc_ref(v___y_2015_);
                    crate::leanh::lean_inc(v___y_2014_);
                    crate::leanh::lean_inc_ref(v___y_2013_);
                    v___x_2025_ = crate::leanh::lean_apply_9(
                        v_ctx_x3f_2009_,
                        v___y_2013_,
                        v___y_2014_,
                        v___y_2015_,
                        v___y_2016_,
                        v___y_2017_,
                        v___y_2018_,
                        v___y_2019_,
                        v___y_2020_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2025_) == 0 {
                        v_a_2026_ = crate::leanh::lean_ctor_get(v___x_2025_, 0);
                        crate::leanh::lean_inc(v_a_2026_);
                        crate::leanh::lean_dec_ref_known(v___x_2025_, 1);
                        v_v_2027_ = lean_array_uget(v_bs_2012_, v_i_2011_);
                        v___x_2028_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2029_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2028_);
                        v_tree_2036_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_2027_, v_assignment_2024_);
                        if crate::leanh::lean_obj_tag(v_a_2026_) == 0 {
                            v_a_2031_ = v_tree_2036_;
                            state = 1;
                            continue;
                        } else {
                            v_val_2037_ = crate::leanh::lean_ctor_get(v_a_2026_, 0);
                            crate::leanh::lean_inc(v_val_2037_);
                            crate::leanh::lean_dec_ref_known(v_a_2026_, 1);
                            v___x_2038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2038_, 0, v_val_2037_);
                            crate::leanh::lean_ctor_set(v___x_2038_, 1, v_tree_2036_);
                            v_a_2031_ = v___x_2038_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2012_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_2009_);
                        v_a_2039_ = crate::leanh::lean_ctor_get(v___x_2025_, 0);
                        v_isSharedCheck_2046_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2025_)) as u8;
                        if v_isSharedCheck_2046_ == 0 {
                            v___x_2041_ = v___x_2025_;
                            v_isShared_2042_ = v_isSharedCheck_2046_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2039_);
                            crate::leanh::lean_dec(v___x_2025_);
                            v___x_2041_ = crate::leanh::lean_box(0);
                            v_isShared_2042_ = v_isSharedCheck_2046_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2032_ = 1usize;
                v___x_2033_ = lean_usize_add(v_i_2011_, v___x_2032_);
                v___x_2034_ = lean_array_uset(v_bs_x27_2029_, v_i_2011_, v_a_2031_);
                v_i_2011_ = v___x_2033_;
                v_bs_2012_ = v___x_2034_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2042_ == 0 {
                    v___x_2044_ = v___x_2041_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
                    v___x_2044_ = v_reuseFailAlloc_2045_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(
    mut v___x_2047_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2048_: *mut crate::leanh::LeanObject,
    mut v_sz_2049_: *mut crate::leanh::LeanObject,
    mut v_i_2050_: *mut crate::leanh::LeanObject,
    mut v_bs_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2061_: usize = 0;
    let mut v_i_boxed_2062_: usize = 0;
    let mut v_res_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2061_ = crate::leanh::lean_unbox_usize(v_sz_2049_);
    crate::leanh::lean_dec(v_sz_2049_);
    v_i_boxed_2062_ = crate::leanh::lean_unbox_usize(v_i_2050_);
    crate::leanh::lean_dec(v_i_2050_);
    v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2047_, v_ctx_x3f_2048_, v_sz_boxed_2061_, v_i_boxed_2062_, v_bs_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
    crate::leanh::lean_dec(v___y_2059_);
    crate::leanh::lean_dec_ref(v___y_2058_);
    crate::leanh::lean_dec(v___y_2057_);
    crate::leanh::lean_dec_ref(v___y_2056_);
    crate::leanh::lean_dec(v___y_2055_);
    crate::leanh::lean_dec_ref(v___y_2054_);
    crate::leanh::lean_dec(v___y_2053_);
    crate::leanh::lean_dec_ref(v___y_2052_);
    crate::leanh::lean_dec_ref(v___x_2047_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(
    mut v___x_2064_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2065_: *mut crate::leanh::LeanObject,
    mut v_x_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
    mut v___y_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v_sz_2080_: usize = 0;
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_a_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_vs_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_sz_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_a_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2066_) == 0 {
                    v_cs_2076_ = crate::leanh::lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2102_ = (!crate::leanh::lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2102_ == 0 {
                        v___x_2078_ = v_x_2066_;
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_2076_);
                        crate::leanh::lean_dec(v_x_2066_);
                        v___x_2078_ = crate::leanh::lean_box(0);
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2103_ = crate::leanh::lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2129_ = (!crate::leanh::lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2105_ = v_x_2066_;
                        v_isShared_2106_ = v_isSharedCheck_2129_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2103_);
                        crate::leanh::lean_dec(v_x_2066_);
                        v___x_2105_ = crate::leanh::lean_box(0);
                        v_isShared_2106_ = v_isSharedCheck_2129_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2080_ = lean_array_size(v_cs_2076_);
                v___x_2081_ = 0usize;
                v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_2064_, v_ctx_x3f_2065_, v_sz_2080_, v___x_2081_, v_cs_2076_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
                if crate::leanh::lean_obj_tag(v___x_2082_) == 0 {
                    v_a_2083_ = crate::leanh::lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2093_ = (!crate::leanh::lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2093_ == 0 {
                        v___x_2085_ = v___x_2082_;
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2083_);
                        crate::leanh::lean_dec(v___x_2082_);
                        v___x_2085_ = crate::leanh::lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2078_);
                    v_a_2094_ = crate::leanh::lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2101_ = (!crate::leanh::lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2096_ = v___x_2082_;
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2094_);
                        crate::leanh::lean_dec(v___x_2082_);
                        v___x_2096_ = crate::leanh::lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2078_, 0, v_a_2083_);
                    v___x_2088_ = v___x_2078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2083_);
                    v___x_2088_ = v_reuseFailAlloc_2092_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2088_);
                    v___x_2090_ = v___x_2085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
                    v___x_2090_ = v_reuseFailAlloc_2091_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2090_;
            }
            5 => {
                if v_isShared_2097_ == 0 {
                    v___x_2099_ = v___x_2096_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2099_;
            }
            7 => {
                v_sz_2107_ = lean_array_size(v_vs_2103_);
                v___x_2108_ = 0usize;
                v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2064_, v_ctx_x3f_2065_, v_sz_2107_, v___x_2108_, v_vs_2103_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
                if crate::leanh::lean_obj_tag(v___x_2109_) == 0 {
                    v_a_2110_ = crate::leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2120_ = (!crate::leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2120_ == 0 {
                        v___x_2112_ = v___x_2109_;
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2110_);
                        crate::leanh::lean_dec(v___x_2109_);
                        v___x_2112_ = crate::leanh::lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2105_);
                    v_a_2121_ = crate::leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2128_ = (!crate::leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2128_ == 0 {
                        v___x_2123_ = v___x_2109_;
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2121_);
                        crate::leanh::lean_dec(v___x_2109_);
                        v___x_2123_ = crate::leanh::lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2106_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2105_, 0, v_a_2110_);
                    v___x_2115_ = v___x_2105_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2119_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2113_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2112_, 0, v___x_2115_);
                    v___x_2117_ = v___x_2112_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
                    v___x_2117_ = v_reuseFailAlloc_2118_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2117_;
            }
            11 => {
                if v_isShared_2124_ == 0 {
                    v___x_2126_ = v___x_2123_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
                    v___x_2126_ = v_reuseFailAlloc_2127_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(
    mut v___x_2130_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2131_: *mut crate::leanh::LeanObject,
    mut v_sz_2132_: usize,
    mut v_i_2133_: usize,
    mut v_bs_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2144_ = lean_usize_dec_lt(v_i_2133_, v_sz_2132_);
                if v___x_2144_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2131_);
                    v___x_2145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2145_, 0, v_bs_2134_);
                    return v___x_2145_;
                } else {
                    v_v_2146_ = lean_array_uget_borrowed(v_bs_2134_, v_i_2133_);
                    crate::leanh::lean_inc(v_v_2146_);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_2131_);
                    v___x_2147_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2130_, v_ctx_x3f_2131_, v_v_2146_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
                    if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        crate::leanh::lean_inc(v_a_2148_);
                        crate::leanh::lean_dec_ref_known(v___x_2147_, 1);
                        v___x_2149_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2150_ = lean_array_uset(v_bs_2134_, v_i_2133_, v___x_2149_);
                        v___x_2151_ = 1usize;
                        v___x_2152_ = lean_usize_add(v_i_2133_, v___x_2151_);
                        v___x_2153_ = lean_array_uset(v_bs_x27_2150_, v_i_2133_, v_a_2148_);
                        v_i_2133_ = v___x_2152_;
                        v_bs_2134_ = v___x_2153_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2134_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_2131_);
                        v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2162_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2147_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2155_);
                            crate::leanh::lean_dec(v___x_2147_);
                            v___x_2157_ = crate::leanh::lean_box(0);
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(
    mut v___x_2163_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2164_: *mut crate::leanh::LeanObject,
    mut v_sz_2165_: *mut crate::leanh::LeanObject,
    mut v_i_2166_: *mut crate::leanh::LeanObject,
    mut v_bs_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
    mut v___y_2175_: *mut crate::leanh::LeanObject,
    mut v___y_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2177_: usize = 0;
    let mut v_i_boxed_2178_: usize = 0;
    let mut v_res_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2177_ = crate::leanh::lean_unbox_usize(v_sz_2165_);
    crate::leanh::lean_dec(v_sz_2165_);
    v_i_boxed_2178_ = crate::leanh::lean_unbox_usize(v_i_2166_);
    crate::leanh::lean_dec(v_i_2166_);
    v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_2163_, v_ctx_x3f_2164_, v_sz_boxed_2177_, v_i_boxed_2178_, v_bs_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
    crate::leanh::lean_dec(v___y_2175_);
    crate::leanh::lean_dec_ref(v___y_2174_);
    crate::leanh::lean_dec(v___y_2173_);
    crate::leanh::lean_dec_ref(v___y_2172_);
    crate::leanh::lean_dec(v___y_2171_);
    crate::leanh::lean_dec_ref(v___y_2170_);
    crate::leanh::lean_dec(v___y_2169_);
    crate::leanh::lean_dec_ref(v___y_2168_);
    crate::leanh::lean_dec_ref(v___x_2163_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(
    mut v___x_2180_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2181_: *mut crate::leanh::LeanObject,
    mut v_x_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2192_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2180_, v_ctx_x3f_2181_, v_x_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
    crate::leanh::lean_dec(v___y_2190_);
    crate::leanh::lean_dec_ref(v___y_2189_);
    crate::leanh::lean_dec(v___y_2188_);
    crate::leanh::lean_dec_ref(v___y_2187_);
    crate::leanh::lean_dec(v___y_2186_);
    crate::leanh::lean_dec_ref(v___y_2185_);
    crate::leanh::lean_dec(v___y_2184_);
    crate::leanh::lean_dec_ref(v___y_2183_);
    crate::leanh::lean_dec_ref(v___x_2180_);
    return v_res_2192_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(
    mut v___x_2193_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2194_: *mut crate::leanh::LeanObject,
    mut v_t_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_2208_: usize = 0;
    let mut v_tailOff_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2215_: usize = 0;
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_a_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_a_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2205_ = crate::leanh::lean_ctor_get(v_t_2195_, 0);
                v_tail_2206_ = crate::leanh::lean_ctor_get(v_t_2195_, 1);
                v_size_2207_ = crate::leanh::lean_ctor_get(v_t_2195_, 2);
                v_shift_2208_ = crate::leanh::lean_ctor_get_usize(v_t_2195_, 4);
                v_tailOff_2209_ = crate::leanh::lean_ctor_get(v_t_2195_, 3);
                v_isSharedCheck_2245_ = (!crate::leanh::lean_is_exclusive(v_t_2195_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v___x_2211_ = v_t_2195_;
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_2209_);
                    crate::leanh::lean_inc(v_size_2207_);
                    crate::leanh::lean_inc(v_tail_2206_);
                    crate::leanh::lean_inc(v_root_2205_);
                    crate::leanh::lean_dec(v_t_2195_);
                    v___x_2211_ = crate::leanh::lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_ctx_x3f_2194_);
                v___x_2213_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2193_, v_ctx_x3f_2194_, v_root_2205_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                if crate::leanh::lean_obj_tag(v___x_2213_) == 0 {
                    v_a_2214_ = crate::leanh::lean_ctor_get(v___x_2213_, 0);
                    crate::leanh::lean_inc(v_a_2214_);
                    crate::leanh::lean_dec_ref_known(v___x_2213_, 1);
                    v_sz_2215_ = lean_array_size(v_tail_2206_);
                    v___x_2216_ = 0usize;
                    v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2193_, v_ctx_x3f_2194_, v_sz_2215_, v___x_2216_, v_tail_2206_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                    if crate::leanh::lean_obj_tag(v___x_2217_) == 0 {
                        v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2228_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2228_ == 0 {
                            v___x_2220_ = v___x_2217_;
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2218_);
                            crate::leanh::lean_dec(v___x_2217_);
                            v___x_2220_ = crate::leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2214_);
                        crate::leanh::lean_del_object(v___x_2211_);
                        crate::leanh::lean_dec(v_tailOff_2209_);
                        crate::leanh::lean_dec(v_size_2207_);
                        v_a_2229_ = crate::leanh::lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2236_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2236_ == 0 {
                            v___x_2231_ = v___x_2217_;
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2229_);
                            crate::leanh::lean_dec(v___x_2217_);
                            v___x_2231_ = crate::leanh::lean_box(0);
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2211_);
                    crate::leanh::lean_dec(v_tailOff_2209_);
                    crate::leanh::lean_dec(v_size_2207_);
                    crate::leanh::lean_dec_ref(v_tail_2206_);
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2194_);
                    v_a_2237_ = crate::leanh::lean_ctor_get(v___x_2213_, 0);
                    v_isSharedCheck_2244_ = (!crate::leanh::lean_is_exclusive(v___x_2213_)) as u8;
                    if v_isSharedCheck_2244_ == 0 {
                        v___x_2239_ = v___x_2213_;
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2237_);
                        crate::leanh::lean_dec(v___x_2213_);
                        v___x_2239_ = crate::leanh::lean_box(0);
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2211_, 1, v_a_2218_);
                    crate::leanh::lean_ctor_set(v___x_2211_, 0, v_a_2214_);
                    v___x_2223_ = v___x_2211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_size_2207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_tailOff_2209_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_2227_, 4, v_shift_2208_);
                    v___x_2223_ = v_reuseFailAlloc_2227_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
                    v___x_2225_ = v_reuseFailAlloc_2226_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2225_;
            }
            5 => {
                if v_isShared_2232_ == 0 {
                    v___x_2234_ = v___x_2231_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2235_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2234_;
            }
            7 => {
                if v_isShared_2240_ == 0 {
                    v___x_2242_ = v___x_2239_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
                    v___x_2242_ = v_reuseFailAlloc_2243_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(
    mut v___x_2246_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2247_: *mut crate::leanh::LeanObject,
    mut v_t_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_2246_, v_ctx_x3f_2247_, v_t_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
    crate::leanh::lean_dec(v___y_2256_);
    crate::leanh::lean_dec_ref(v___y_2255_);
    crate::leanh::lean_dec(v___y_2254_);
    crate::leanh::lean_dec_ref(v___y_2253_);
    crate::leanh::lean_dec(v___y_2252_);
    crate::leanh::lean_dec_ref(v___y_2251_);
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec_ref(v___y_2249_);
    crate::leanh::lean_dec_ref(v___x_2246_);
    return v_res_2258_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_enabled_2292_: u8 = 0;
    let mut v_assignment_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_a_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2271_ = lean_st_ref_get(v___y_2259_);
                v_infoState_2272_ = crate::leanh::lean_ctor_get(v___x_2271_, 7);
                crate::leanh::lean_inc_ref(v_infoState_2272_);
                crate::leanh::lean_dec(v___x_2271_);
                v_trees_2273_ = crate::leanh::lean_ctor_get(v_infoState_2272_, 2);
                crate::leanh::lean_inc_ref(v_trees_2273_);
                v___x_2274_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_2272_, v_ctx_x3f_2260_, v_trees_2273_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2259_);
                crate::leanh::lean_dec_ref(v_infoState_2272_);
                if crate::leanh::lean_obj_tag(v___x_2274_) == 0 {
                    v_a_2275_ = crate::leanh::lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2313_ = (!crate::leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2313_ == 0 {
                        v___x_2277_ = v___x_2274_;
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2275_);
                        crate::leanh::lean_dec(v___x_2274_);
                        v___x_2277_ = crate::leanh::lean_box(0);
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2268_);
                    v_a_2314_ = crate::leanh::lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2321_ = (!crate::leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2274_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2314_);
                        crate::leanh::lean_dec(v___x_2274_);
                        v___x_2316_ = crate::leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2279_ = lean_st_ref_take(v___y_2259_);
                v_infoState_2280_ = crate::leanh::lean_ctor_get(v___x_2279_, 7);
                v_env_2281_ = crate::leanh::lean_ctor_get(v___x_2279_, 0);
                v_nextMacroScope_2282_ = crate::leanh::lean_ctor_get(v___x_2279_, 1);
                v_ngen_2283_ = crate::leanh::lean_ctor_get(v___x_2279_, 2);
                v_auxDeclNGen_2284_ = crate::leanh::lean_ctor_get(v___x_2279_, 3);
                v_traceState_2285_ = crate::leanh::lean_ctor_get(v___x_2279_, 4);
                v_cache_2286_ = crate::leanh::lean_ctor_get(v___x_2279_, 5);
                v_messages_2287_ = crate::leanh::lean_ctor_get(v___x_2279_, 6);
                v_snapshotTasks_2288_ = crate::leanh::lean_ctor_get(v___x_2279_, 8);
                v_isSharedCheck_2312_ = (!crate::leanh::lean_is_exclusive(v___x_2279_)) as u8;
                if v_isSharedCheck_2312_ == 0 {
                    v___x_2290_ = v___x_2279_;
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2288_);
                    crate::leanh::lean_inc(v_infoState_2280_);
                    crate::leanh::lean_inc(v_messages_2287_);
                    crate::leanh::lean_inc(v_cache_2286_);
                    crate::leanh::lean_inc(v_traceState_2285_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2284_);
                    crate::leanh::lean_inc(v_ngen_2283_);
                    crate::leanh::lean_inc(v_nextMacroScope_2282_);
                    crate::leanh::lean_inc(v_env_2281_);
                    crate::leanh::lean_dec(v___x_2279_);
                    v___x_2290_ = crate::leanh::lean_box(0);
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_2292_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2280_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_2293_ = crate::leanh::lean_ctor_get(v_infoState_2280_, 0);
                v_lazyAssignment_2294_ = crate::leanh::lean_ctor_get(v_infoState_2280_, 1);
                v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v_infoState_2280_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v_unused_2311_ = crate::leanh::lean_ctor_get(v_infoState_2280_, 2);
                    crate::leanh::lean_dec(v_unused_2311_);
                    v___x_2296_ = v_infoState_2280_;
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_2294_);
                    crate::leanh::lean_inc(v_assignment_2293_);
                    crate::leanh::lean_dec(v_infoState_2280_);
                    v___x_2296_ = crate::leanh::lean_box(0);
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2298_ = l_Lean_PersistentArray_append___redArg(v_a_2268_, v_a_2275_);
                crate::leanh::lean_dec(v_a_2275_);
                if v_isShared_2297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2296_, 2, v___x_2298_);
                    v___x_2300_ = v___x_2296_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_assignment_2293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_lazyAssignment_2294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 2, v___x_2298_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2309_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_2292_,
                    );
                    v___x_2300_ = v_reuseFailAlloc_2309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2290_, 7, v___x_2300_);
                    v___x_2302_ = v___x_2290_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_env_2281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_cache_2286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 6, v_messages_2287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 7, v___x_2300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2288_);
                    v___x_2302_ = v_reuseFailAlloc_2308_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2303_ = lean_st_ref_set(v___y_2259_, v___x_2302_);
                v___x_2304_ = crate::leanh::lean_box(0);
                if v_isShared_2278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2304_);
                    v___x_2306_ = v___x_2277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2306_;
            }
            7 => {
                if v_isShared_2317_ == 0 {
                    v___x_2319_ = v___x_2316_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2322_, v_ctx_x3f_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v_a_2331_, v_a_x3f_2332_);
    crate::leanh::lean_dec(v_a_x3f_2332_);
    crate::leanh::lean_dec_ref(v___y_2330_);
    crate::leanh::lean_dec(v___y_2329_);
    crate::leanh::lean_dec_ref(v___y_2328_);
    crate::leanh::lean_dec(v___y_2327_);
    crate::leanh::lean_dec_ref(v___y_2326_);
    crate::leanh::lean_dec(v___y_2325_);
    crate::leanh::lean_dec_ref(v___y_2324_);
    crate::leanh::lean_dec(v___y_2322_);
    return v_res_2334_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2348_: u8 = 0;
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2371_: u8 = 0;
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_a_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_unused_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_st_ref_get(v___y_2344_);
                v_infoState_2347_ = crate::leanh::lean_ctor_get(v___x_2346_, 7);
                crate::leanh::lean_inc_ref(v_infoState_2347_);
                crate::leanh::lean_dec(v___x_2346_);
                v_enabled_2348_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_2347_);
                if v_enabled_2348_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2336_);
                    crate::leanh::lean_inc(v___y_2344_);
                    crate::leanh::lean_inc_ref(v___y_2343_);
                    crate::leanh::lean_inc(v___y_2342_);
                    crate::leanh::lean_inc_ref(v___y_2341_);
                    crate::leanh::lean_inc(v___y_2340_);
                    crate::leanh::lean_inc_ref(v___y_2339_);
                    crate::leanh::lean_inc(v___y_2338_);
                    crate::leanh::lean_inc_ref(v___y_2337_);
                    v___x_2349_ = crate::leanh::lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2349_;
                } else {
                    v___x_2350_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2344_);
                    v_a_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 0);
                    crate::leanh::lean_inc(v_a_2351_);
                    crate::leanh::lean_dec_ref(v___x_2350_);
                    crate::leanh::lean_inc(v___y_2344_);
                    crate::leanh::lean_inc_ref(v___y_2343_);
                    crate::leanh::lean_inc(v___y_2342_);
                    crate::leanh::lean_inc_ref(v___y_2341_);
                    crate::leanh::lean_inc(v___y_2340_);
                    crate::leanh::lean_inc_ref(v___y_2339_);
                    crate::leanh::lean_inc(v___y_2338_);
                    crate::leanh::lean_inc_ref(v___y_2337_);
                    v_r_2352_ = crate::leanh::lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_2352_) == 0 {
                        v_a_2353_ = crate::leanh::lean_ctor_get(v_r_2352_, 0);
                        v_isSharedCheck_2377_ = (!crate::leanh::lean_is_exclusive(v_r_2352_)) as u8;
                        if v_isSharedCheck_2377_ == 0 {
                            v___x_2355_ = v_r_2352_;
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2353_);
                            crate::leanh::lean_dec(v_r_2352_);
                            v___x_2355_ = crate::leanh::lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2378_ = crate::leanh::lean_ctor_get(v_r_2352_, 0);
                        crate::leanh::lean_inc(v_a_2378_);
                        crate::leanh::lean_dec_ref_known(v_r_2352_, 1);
                        v___x_2379_ = crate::leanh::lean_box(0);
                        v___x_2380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2379_);
                        if crate::leanh::lean_obj_tag(v___x_2380_) == 0 {
                            v_isSharedCheck_2387_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2387_ == 0 {
                                v_unused_2388_ = crate::leanh::lean_ctor_get(v___x_2380_, 0);
                                crate::leanh::lean_dec(v_unused_2388_);
                                v___x_2382_ = v___x_2380_;
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2380_);
                                v___x_2382_ = crate::leanh::lean_box(0);
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2378_);
                            v_a_2389_ = crate::leanh::lean_ctor_get(v___x_2380_, 0);
                            v_isSharedCheck_2396_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2396_ == 0 {
                                v___x_2391_ = v___x_2380_;
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2389_);
                                crate::leanh::lean_dec(v___x_2380_);
                                v___x_2391_ = crate::leanh::lean_box(0);
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2353_);
                if v_isShared_2356_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2355_, 1);
                    v___x_2358_ = v___x_2355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2358_);
                crate::leanh::lean_dec_ref(v___x_2358_);
                if crate::leanh::lean_obj_tag(v___x_2359_) == 0 {
                    v_isSharedCheck_2366_ = (!crate::leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v_unused_2367_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                        crate::leanh::lean_dec(v_unused_2367_);
                        v___x_2361_ = v___x_2359_;
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2359_);
                        v___x_2361_ = crate::leanh::lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2353_);
                    v_a_2368_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
                    v_isSharedCheck_2375_ = (!crate::leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2375_ == 0 {
                        v___x_2370_ = v___x_2359_;
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2368_);
                        crate::leanh::lean_dec(v___x_2359_);
                        v___x_2370_ = crate::leanh::lean_box(0);
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2361_, 0, v_a_2353_);
                    v___x_2364_ = v___x_2361_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2353_);
                    v___x_2364_ = v_reuseFailAlloc_2365_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2364_;
            }
            5 => {
                if v_isShared_2371_ == 0 {
                    v___x_2373_ = v___x_2370_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
                    v___x_2373_ = v_reuseFailAlloc_2374_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2373_;
            }
            7 => {
                if v_isShared_2383_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2382_, 1);
                    crate::leanh::lean_ctor_set(v___x_2382_, 0, v_a_2378_);
                    v___x_2385_ = v___x_2382_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2385_;
            }
            9 => {
                if v_isShared_2392_ == 0 {
                    v___x_2394_ = v___x_2391_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
                    v___x_2394_ = v_reuseFailAlloc_2395_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(
    mut v_x_2397_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2397_, v_ctx_x3f_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
    crate::leanh::lean_dec(v___y_2406_);
    crate::leanh::lean_dec_ref(v___y_2405_);
    crate::leanh::lean_dec(v___y_2404_);
    crate::leanh::lean_dec_ref(v___y_2403_);
    crate::leanh::lean_dec(v___y_2402_);
    crate::leanh::lean_dec_ref(v___y_2401_);
    crate::leanh::lean_dec(v___y_2400_);
    crate::leanh::lean_dec_ref(v___y_2399_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(
    mut v_x_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2420_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0;
    v___x_2421_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2410_, v___f_2420_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(
    mut v_x_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(
            v_x_2422_,
            v___y_2423_,
            v___y_2424_,
            v___y_2425_,
            v___y_2426_,
            v___y_2427_,
            v___y_2428_,
            v___y_2429_,
            v___y_2430_,
        );
    crate::leanh::lean_dec(v___y_2430_);
    crate::leanh::lean_dec_ref(v___y_2429_);
    crate::leanh::lean_dec(v___y_2428_);
    crate::leanh::lean_dec_ref(v___y_2427_);
    crate::leanh::lean_dec(v___y_2426_);
    crate::leanh::lean_dec_ref(v___y_2425_);
    crate::leanh::lean_dec(v___y_2424_);
    crate::leanh::lean_dec_ref(v___y_2423_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(
    mut v_00_u03b1_2433_: *mut crate::leanh::LeanObject,
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(
            v_x_2434_,
            v___y_2435_,
            v___y_2436_,
            v___y_2437_,
            v___y_2438_,
            v___y_2439_,
            v___y_2440_,
            v___y_2441_,
            v___y_2442_,
        );
    return v___x_2444_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(
    mut v_00_u03b1_2445_: *mut crate::leanh::LeanObject,
    mut v_x_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2456_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(
        v_00_u03b1_2445_,
        v_x_2446_,
        v___y_2447_,
        v___y_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
        v___y_2452_,
        v___y_2453_,
        v___y_2454_,
    );
    crate::leanh::lean_dec(v___y_2454_);
    crate::leanh::lean_dec_ref(v___y_2453_);
    crate::leanh::lean_dec(v___y_2452_);
    crate::leanh::lean_dec_ref(v___y_2451_);
    crate::leanh::lean_dec(v___y_2450_);
    crate::leanh::lean_dec_ref(v___y_2449_);
    crate::leanh::lean_dec(v___y_2448_);
    crate::leanh::lean_dec_ref(v___y_2447_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalClassical(
    mut v_stx_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2469_ = l_Lean_Elab_Tactic_evalClassical___closed__0;
    v___x_2470_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed as *mut core::ffi::c_void, 13, 4);
    crate::leanh::lean_closure_set(v___x_2470_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2470_, 1, v___x_2468_);
    crate::leanh::lean_closure_set(v___x_2470_, 2, v___x_2469_);
    crate::leanh::lean_closure_set(v___x_2470_, 3, v_stx_2458_);
    v___x_2471_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2471_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2471_, 1, v___x_2470_);
    v___x_2472_ =
        l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
            v___x_2471_,
            v_a_2459_,
            v_a_2460_,
            v_a_2461_,
            v_a_2462_,
            v_a_2463_,
            v_a_2464_,
            v_a_2465_,
            v_a_2466_,
        );
    return v___x_2472_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalClassical___boxed(
    mut v_stx_2473_: *mut crate::leanh::LeanObject,
    mut v_a_2474_: *mut crate::leanh::LeanObject,
    mut v_a_2475_: *mut crate::leanh::LeanObject,
    mut v_a_2476_: *mut crate::leanh::LeanObject,
    mut v_a_2477_: *mut crate::leanh::LeanObject,
    mut v_a_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l_Lean_Elab_Tactic_evalClassical(
        v_stx_2473_,
        v_a_2474_,
        v_a_2475_,
        v_a_2476_,
        v_a_2477_,
        v_a_2478_,
        v_a_2479_,
        v_a_2480_,
        v_a_2481_,
    );
    crate::leanh::lean_dec(v_a_2481_);
    crate::leanh::lean_dec_ref(v_a_2480_);
    crate::leanh::lean_dec(v_a_2479_);
    crate::leanh::lean_dec_ref(v_a_2478_);
    crate::leanh::lean_dec(v_a_2477_);
    crate::leanh::lean_dec_ref(v_a_2476_);
    crate::leanh::lean_dec(v_a_2475_);
    crate::leanh::lean_dec_ref(v_a_2474_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2484_: *mut crate::leanh::LeanObject,
    mut v_stx_2485_: *mut crate::leanh::LeanObject,
    mut v_act_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_2485_, v_act_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2497_: *mut crate::leanh::LeanObject,
    mut v_stx_2498_: *mut crate::leanh::LeanObject,
    mut v_act_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
    mut v___y_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_2497_, v_stx_2498_, v_act_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
    crate::leanh::lean_dec(v___y_2507_);
    crate::leanh::lean_dec_ref(v___y_2506_);
    crate::leanh::lean_dec(v___y_2505_);
    crate::leanh::lean_dec_ref(v___y_2504_);
    crate::leanh::lean_dec(v___y_2503_);
    crate::leanh::lean_dec_ref(v___y_2502_);
    crate::leanh::lean_dec(v___y_2501_);
    crate::leanh::lean_dec_ref(v___y_2500_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(
    mut v_00_u03b1_2510_: *mut crate::leanh::LeanObject,
    mut v_split_2511_: *mut crate::leanh::LeanObject,
    mut v_act_2512_: *mut crate::leanh::LeanObject,
    mut v_stx_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_2511_, v_act_2512_, v_stx_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
    return v___x_2523_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(
    mut v_00_u03b1_2524_: *mut crate::leanh::LeanObject,
    mut v_split_2525_: *mut crate::leanh::LeanObject,
    mut v_act_2526_: *mut crate::leanh::LeanObject,
    mut v_stx_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_2524_, v_split_2525_, v_act_2526_, v_stx_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
    crate::leanh::lean_dec(v___y_2535_);
    crate::leanh::lean_dec_ref(v___y_2534_);
    crate::leanh::lean_dec(v___y_2533_);
    crate::leanh::lean_dec_ref(v___y_2532_);
    crate::leanh::lean_dec(v___y_2531_);
    crate::leanh::lean_dec_ref(v___y_2530_);
    crate::leanh::lean_dec(v___y_2529_);
    crate::leanh::lean_dec_ref(v___y_2528_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_2543_, v___y_2544_, v___y_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
    crate::leanh::lean_dec(v___y_2555_);
    crate::leanh::lean_dec_ref(v___y_2554_);
    crate::leanh::lean_dec(v___y_2553_);
    crate::leanh::lean_dec_ref(v___y_2552_);
    crate::leanh::lean_dec(v___y_2551_);
    crate::leanh::lean_dec_ref(v___y_2550_);
    crate::leanh::lean_dec(v___y_2549_);
    crate::leanh::lean_dec_ref(v___y_2548_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(
    mut v___y_2558_: *mut crate::leanh::LeanObject,
    mut v___y_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2565_);
    return v___x_2567_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(
    mut v___y_2568_: *mut crate::leanh::LeanObject,
    mut v___y_2569_: *mut crate::leanh::LeanObject,
    mut v___y_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    crate::leanh::lean_dec(v___y_2575_);
    crate::leanh::lean_dec_ref(v___y_2574_);
    crate::leanh::lean_dec(v___y_2573_);
    crate::leanh::lean_dec_ref(v___y_2572_);
    crate::leanh::lean_dec(v___y_2571_);
    crate::leanh::lean_dec_ref(v___y_2570_);
    crate::leanh::lean_dec(v___y_2569_);
    crate::leanh::lean_dec_ref(v___y_2568_);
    return v_res_2577_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(
    mut v_00_u03b1_2578_: *mut crate::leanh::LeanObject,
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2580_: *mut crate::leanh::LeanObject,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2579_, v_ctx_x3f_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
    return v___x_2590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(
    mut v_00_u03b1_2591_: *mut crate::leanh::LeanObject,
    mut v_x_2592_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2603_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_2591_, v_x_2592_, v_ctx_x3f_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
    crate::leanh::lean_dec(v___y_2601_);
    crate::leanh::lean_dec_ref(v___y_2600_);
    crate::leanh::lean_dec(v___y_2599_);
    crate::leanh::lean_dec_ref(v___y_2598_);
    crate::leanh::lean_dec(v___y_2597_);
    crate::leanh::lean_dec_ref(v___y_2596_);
    crate::leanh::lean_dec(v___y_2595_);
    crate::leanh::lean_dec_ref(v___y_2594_);
    return v_res_2603_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2622_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4;
    v___x_2623_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2624_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalClassical___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2625_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2621_,
        v___x_2622_,
        v___x_2623_,
        v___x_2624_,
    );
    return v___x_2625_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(
    mut v_a_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    return v_res_2627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2630_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_2629_);
    return v___x_2630_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(
    mut v_a_2631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2632_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    return v_res_2632_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Classical(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Classical(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Classical(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Classical(builtin);
}
