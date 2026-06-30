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
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        10854111772627758120 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
            as *mut leanh::LeanObject,
        4643704380461739942 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_addInstance___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((10 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_classical___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalClassical___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalTactic___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalClassical___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalClassical___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut leanh::LeanObject,1538718060909595165 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut leanh::LeanObject,3595078106460476937 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0(
    mut v_x_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1318_ = leanh::lean_ctor_get(v_x_1317_, 0);
    leanh::lean_inc(v_fst_1318_);
    return v_fst_1318_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed(
    mut v_x_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_Elab_Tactic_classical___redArg___lam__0(v_x_1319_);
    leanh::lean_dec_ref(v_x_1319_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1(
    mut v___x_1321_: *mut leanh::LeanObject,
    mut v_x_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_1321_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed(
    mut v___x_1323_: *mut leanh::LeanObject,
    mut v_x_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lean_Elab_Tactic_classical___redArg___lam__1(v___x_1323_, v_x_1324_);
    leanh::lean_dec(v_x_1324_);
    leanh::lean_dec(v___x_1323_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__2(
    mut v_toFunctor_1326_: *mut leanh::LeanObject,
    mut v___x_1327_: *mut leanh::LeanObject,
    mut v_modifyEnv_1328_: *mut leanh::LeanObject,
    mut v_inst_1329_: *mut leanh::LeanObject,
    mut v_t_1330_: *mut leanh::LeanObject,
    mut v___f_1331_: *mut leanh::LeanObject,
    mut v_____r_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1333_ = leanh::lean_ctor_get(v_toFunctor_1326_, 0);
    leanh::lean_inc(v_map_1333_);
    leanh::lean_dec_ref(v_toFunctor_1326_);
    v___x_1334_ = leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_popScope as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1334_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1334_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1334_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1334_, 3, v___x_1327_);
    v___x_1335_ = leanh::lean_apply_1(v_modifyEnv_1328_, v___x_1334_);
    v___f_1336_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1336_, 0, v___x_1335_);
    v_y_1337_ = leanh::lean_apply_4(
        v_inst_1329_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_t_1330_,
        v___f_1336_,
    );
    v___x_1338_ = leanh::lean_apply_4(
        v_map_1333_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1331_,
        v_y_1337_,
    );
    return v___x_1338_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__3(
    mut v_inst_1349_: *mut leanh::LeanObject,
    mut v_toBind_1350_: *mut leanh::LeanObject,
    mut v___f_1351_: *mut leanh::LeanObject,
    mut v_____r_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3;
    v___x_1354_ = leanh::lean_apply_2(v_inst_1349_, leanh::lean_box(0), v___x_1353_);
    v___x_1355_ = leanh::lean_apply_4(
        v_toBind_1350_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1354_,
        v___f_1351_,
    );
    return v___x_1355_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lean_Meta_instanceExtension;
    v___x_1358_ = leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_pushScope as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1358_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1358_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1358_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1358_, 3, v___x_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg(
    mut v_inst_1359_: *mut leanh::LeanObject,
    mut v_inst_1360_: *mut leanh::LeanObject,
    mut v_inst_1361_: *mut leanh::LeanObject,
    mut v_inst_1362_: *mut leanh::LeanObject,
    mut v_t_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1364_ = leanh::lean_ctor_get(v_inst_1359_, 0);
    leanh::lean_inc_ref(v_toApplicative_1364_);
    v_toBind_1365_ = leanh::lean_ctor_get(v_inst_1359_, 1);
    leanh::lean_inc_n(v_toBind_1365_, 2);
    leanh::lean_dec_ref(v_inst_1359_);
    v_modifyEnv_1366_ = leanh::lean_ctor_get(v_inst_1360_, 1);
    leanh::lean_inc_n(v_modifyEnv_1366_, 2);
    leanh::lean_dec_ref(v_inst_1360_);
    v_toFunctor_1367_ = leanh::lean_ctor_get(v_toApplicative_1364_, 0);
    leanh::lean_inc_ref(v_toFunctor_1367_);
    leanh::lean_dec_ref(v_toApplicative_1364_);
    v___f_1368_ = l_Lean_Elab_Tactic_classical___redArg___closed__0;
    v___x_1369_ = l_Lean_Meta_instanceExtension;
    v___x_1370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_classical___redArg___closed__1,
    );
    v___x_1371_ = leanh::lean_apply_1(v_modifyEnv_1366_, v___x_1370_);
    v___f_1372_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1372_, 0, v_toFunctor_1367_);
    leanh::lean_closure_set(v___f_1372_, 1, v___x_1369_);
    leanh::lean_closure_set(v___f_1372_, 2, v_modifyEnv_1366_);
    leanh::lean_closure_set(v___f_1372_, 3, v_inst_1361_);
    leanh::lean_closure_set(v___f_1372_, 4, v_t_1363_);
    leanh::lean_closure_set(v___f_1372_, 5, v___f_1368_);
    v___f_1373_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1373_, 0, v_inst_1362_);
    leanh::lean_closure_set(v___f_1373_, 1, v_toBind_1365_);
    leanh::lean_closure_set(v___f_1373_, 2, v___f_1372_);
    v___x_1374_ = leanh::lean_apply_4(
        v_toBind_1365_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1371_,
        v___f_1373_,
    );
    return v___x_1374_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical(
    mut v_m_1375_: *mut leanh::LeanObject,
    mut v_00_u03b1_1376_: *mut leanh::LeanObject,
    mut v_inst_1377_: *mut leanh::LeanObject,
    mut v_inst_1378_: *mut leanh::LeanObject,
    mut v_inst_1379_: *mut leanh::LeanObject,
    mut v_inst_1380_: *mut leanh::LeanObject,
    mut v_t_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___x_1384_: *mut leanh::LeanObject,
    mut v___x_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___x_1387_: *mut leanh::LeanObject,
    mut v_a_x3f_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1423_: u8 = 0;
    let mut v_unused_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_st_ref_take(v___y_1383_);
                v_env_1391_ = leanh::lean_ctor_get(v___x_1390_, 0);
                v_nextMacroScope_1392_ = leanh::lean_ctor_get(v___x_1390_, 1);
                v_ngen_1393_ = leanh::lean_ctor_get(v___x_1390_, 2);
                v_auxDeclNGen_1394_ = leanh::lean_ctor_get(v___x_1390_, 3);
                v_traceState_1395_ = leanh::lean_ctor_get(v___x_1390_, 4);
                v_messages_1396_ = leanh::lean_ctor_get(v___x_1390_, 6);
                v_infoState_1397_ = leanh::lean_ctor_get(v___x_1390_, 7);
                v_snapshotTasks_1398_ = leanh::lean_ctor_get(v___x_1390_, 8);
                v_isSharedCheck_1423_ = (!leanh::lean_is_exclusive(v___x_1390_)) as u8;
                if v_isSharedCheck_1423_ == 0 {
                    v_unused_1424_ = leanh::lean_ctor_get(v___x_1390_, 5);
                    leanh::lean_dec(v_unused_1424_);
                    v___x_1400_ = v___x_1390_;
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1398_);
                    leanh::lean_inc(v_infoState_1397_);
                    leanh::lean_inc(v_messages_1396_);
                    leanh::lean_inc(v_traceState_1395_);
                    leanh::lean_inc(v_auxDeclNGen_1394_);
                    leanh::lean_inc(v_ngen_1393_);
                    leanh::lean_inc(v_nextMacroScope_1392_);
                    leanh::lean_inc(v_env_1391_);
                    leanh::lean_dec(v___x_1390_);
                    v___x_1400_ = leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1402_ = l_Lean_ScopedEnvExtension_popScope___redArg(v___x_1384_, v_env_1391_);
                if v_isShared_1401_ == 0 {
                    leanh::lean_ctor_set(v___x_1400_, 5, v___x_1385_);
                    leanh::lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1422_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_nextMacroScope_1392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_ngen_1393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_auxDeclNGen_1394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_traceState_1395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 5, v___x_1385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_messages_1396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_infoState_1397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_snapshotTasks_1398_);
                    v___x_1404_ = v_reuseFailAlloc_1422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1405_ = lean_st_ref_set(v___y_1383_, v___x_1404_);
                v___x_1406_ = lean_st_ref_take(v___y_1386_);
                v_mctx_1407_ = leanh::lean_ctor_get(v___x_1406_, 0);
                v_zetaDeltaFVarIds_1408_ = leanh::lean_ctor_get(v___x_1406_, 2);
                v_postponed_1409_ = leanh::lean_ctor_get(v___x_1406_, 3);
                v_diag_1410_ = leanh::lean_ctor_get(v___x_1406_, 4);
                v_isSharedCheck_1420_ = (!leanh::lean_is_exclusive(v___x_1406_)) as u8;
                if v_isSharedCheck_1420_ == 0 {
                    v_unused_1421_ = leanh::lean_ctor_get(v___x_1406_, 1);
                    leanh::lean_dec(v_unused_1421_);
                    v___x_1412_ = v___x_1406_;
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1410_);
                    leanh::lean_inc(v_postponed_1409_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1408_);
                    leanh::lean_inc(v_mctx_1407_);
                    leanh::lean_dec(v___x_1406_);
                    v___x_1412_ = leanh::lean_box(0);
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1413_ == 0 {
                    leanh::lean_ctor_set(v___x_1412_, 1, v___x_1387_);
                    v___x_1415_ = v___x_1412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_mctx_1407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1387_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1419_,
                        2,
                        v_zetaDeltaFVarIds_1408_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_postponed_1409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_diag_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1416_ = lean_st_ref_set(v___y_1386_, v___x_1415_);
                v___x_1417_ = leanh::lean_box(0);
                v___x_1418_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___x_1426_: *mut leanh::LeanObject,
    mut v___x_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___x_1429_: *mut leanh::LeanObject,
    mut v_a_x3f_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1425_, v___x_1426_, v___x_1427_, v___y_1428_, v___x_1429_, v_a_x3f_1430_);
    leanh::lean_dec(v_a_x3f_1430_);
    leanh::lean_dec(v___y_1428_);
    leanh::lean_dec(v___y_1425_);
    return v_res_1432_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1433_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
    v___x_1435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1437_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1437_, 0, v___x_1436_);
    leanh::lean_ctor_set(v___x_1437_, 1, v___x_1436_);
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1439_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 1, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 2, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 3, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 4, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 5, v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
    mut v_t_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_unused_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_a_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_unused_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_reuseFailAlloc_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1522_: u8 = 0;
    let mut v_unused_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1450_ = lean_st_ref_take(v___y_1448_);
                v_env_1451_ = leanh::lean_ctor_get(v___x_1450_, 0);
                v_nextMacroScope_1452_ = leanh::lean_ctor_get(v___x_1450_, 1);
                v_ngen_1453_ = leanh::lean_ctor_get(v___x_1450_, 2);
                v_auxDeclNGen_1454_ = leanh::lean_ctor_get(v___x_1450_, 3);
                v_traceState_1455_ = leanh::lean_ctor_get(v___x_1450_, 4);
                v_messages_1456_ = leanh::lean_ctor_get(v___x_1450_, 6);
                v_infoState_1457_ = leanh::lean_ctor_get(v___x_1450_, 7);
                v_snapshotTasks_1458_ = leanh::lean_ctor_get(v___x_1450_, 8);
                v_isSharedCheck_1525_ = (!leanh::lean_is_exclusive(v___x_1450_)) as u8;
                if v_isSharedCheck_1525_ == 0 {
                    v_unused_1526_ = leanh::lean_ctor_get(v___x_1450_, 5);
                    leanh::lean_dec(v_unused_1526_);
                    v___x_1460_ = v___x_1450_;
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1458_);
                    leanh::lean_inc(v_infoState_1457_);
                    leanh::lean_inc(v_messages_1456_);
                    leanh::lean_inc(v_traceState_1455_);
                    leanh::lean_inc(v_auxDeclNGen_1454_);
                    leanh::lean_inc(v_ngen_1453_);
                    leanh::lean_inc(v_nextMacroScope_1452_);
                    leanh::lean_inc(v_env_1451_);
                    leanh::lean_dec(v___x_1450_);
                    v___x_1460_ = leanh::lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1462_ = l_Lean_Meta_instanceExtension;
                v___x_1463_ =
                    l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_1462_, v_env_1451_);
                v___x_1464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
                if v_isShared_1461_ == 0 {
                    leanh::lean_ctor_set(v___x_1460_, 5, v___x_1464_);
                    leanh::lean_ctor_set(v___x_1460_, 0, v___x_1463_);
                    v___x_1466_ = v___x_1460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_traceState_1455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 5, v___x_1464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_messages_1456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_infoState_1457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_snapshotTasks_1458_);
                    v___x_1466_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1467_ = lean_st_ref_set(v___y_1448_, v___x_1466_);
                v___x_1468_ = lean_st_ref_take(v___y_1446_);
                v_mctx_1469_ = leanh::lean_ctor_get(v___x_1468_, 0);
                v_zetaDeltaFVarIds_1470_ = leanh::lean_ctor_get(v___x_1468_, 2);
                v_postponed_1471_ = leanh::lean_ctor_get(v___x_1468_, 3);
                v_diag_1472_ = leanh::lean_ctor_get(v___x_1468_, 4);
                v_isSharedCheck_1522_ = (!leanh::lean_is_exclusive(v___x_1468_)) as u8;
                if v_isSharedCheck_1522_ == 0 {
                    v_unused_1523_ = leanh::lean_ctor_get(v___x_1468_, 1);
                    leanh::lean_dec(v_unused_1523_);
                    v___x_1474_ = v___x_1468_;
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1472_);
                    leanh::lean_inc(v_postponed_1471_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1470_);
                    leanh::lean_inc(v_mctx_1469_);
                    leanh::lean_dec(v___x_1468_);
                    v___x_1474_ = leanh::lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1476_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set(v___x_1474_, 1, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_mctx_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1476_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1521_,
                        2,
                        v_zetaDeltaFVarIds_1470_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_postponed_1471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_diag_1472_);
                    v___x_1478_ = v_reuseFailAlloc_1521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1479_ = lean_st_ref_set(v___y_1446_, v___x_1478_);
                v___x_1480_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2;
                v___x_1481_ = 1;
                v___x_1482_ = leanh::lean_unsigned_to_nat(10);
                v___x_1483_ = l_Lean_Meta_addInstance(
                    v___x_1480_,
                    v___x_1481_,
                    v___x_1482_,
                    v___y_1445_,
                    v___y_1446_,
                    v___y_1447_,
                    v___y_1448_,
                );
                if leanh::lean_obj_tag(v___x_1483_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1483_, 1);
                    leanh::lean_inc(v___y_1448_);
                    leanh::lean_inc_ref(v___y_1447_);
                    leanh::lean_inc(v___y_1446_);
                    leanh::lean_inc_ref(v___y_1445_);
                    leanh::lean_inc(v___y_1444_);
                    leanh::lean_inc_ref(v___y_1443_);
                    leanh::lean_inc(v___y_1442_);
                    leanh::lean_inc_ref(v___y_1441_);
                    v_r_1484_ = leanh::lean_apply_9(
                        v_t_1440_,
                        v___y_1441_,
                        v___y_1442_,
                        v___y_1443_,
                        v___y_1444_,
                        v___y_1445_,
                        v___y_1446_,
                        v___y_1447_,
                        v___y_1448_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_1484_) == 0 {
                        v_a_1485_ = leanh::lean_ctor_get(v_r_1484_, 0);
                        v_isSharedCheck_1501_ = (!leanh::lean_is_exclusive(v_r_1484_)) as u8;
                        if v_isSharedCheck_1501_ == 0 {
                            v___x_1487_ = v_r_1484_;
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1485_);
                            leanh::lean_dec(v_r_1484_);
                            v___x_1487_ = leanh::lean_box(0);
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1502_ = leanh::lean_ctor_get(v_r_1484_, 0);
                        leanh::lean_inc(v_a_1502_);
                        leanh::lean_dec_ref_known(v_r_1484_, 1);
                        v___x_1503_ = leanh::lean_box(0);
                        v___x_1504_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1503_);
                        v_isSharedCheck_1511_ =
                            (!leanh::lean_is_exclusive(v___x_1504_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v_unused_1512_ = leanh::lean_ctor_get(v___x_1504_, 0);
                            leanh::lean_dec(v_unused_1512_);
                            v___x_1506_ = v___x_1504_;
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1504_);
                            v___x_1506_ = leanh::lean_box(0);
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_t_1440_);
                    v_a_1513_ = leanh::lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1520_ = (!leanh::lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1520_ == 0 {
                        v___x_1515_ = v___x_1483_;
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1513_);
                        leanh::lean_dec(v___x_1483_);
                        v___x_1515_ = leanh::lean_box(0);
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_1485_);
                if v_isShared_1488_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1487_, 1);
                    v___x_1490_ = v___x_1487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1485_);
                    v___x_1490_ = v_reuseFailAlloc_1500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1491_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1490_);
                leanh::lean_dec_ref(v___x_1490_);
                v_isSharedCheck_1498_ = (!leanh::lean_is_exclusive(v___x_1491_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v_unused_1499_ = leanh::lean_ctor_get(v___x_1491_, 0);
                    leanh::lean_dec(v_unused_1499_);
                    v___x_1493_ = v___x_1491_;
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1491_);
                    v___x_1493_ = leanh::lean_box(0);
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1494_ == 0 {
                    leanh::lean_ctor_set(v___x_1493_, 0, v_a_1485_);
                    v___x_1496_ = v___x_1493_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1485_);
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
                    leanh::lean_ctor_set_tag(v___x_1506_, 1);
                    leanh::lean_ctor_set(v___x_1506_, 0, v_a_1502_);
                    v___x_1509_ = v___x_1506_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1502_);
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
                    v_reuseFailAlloc_1519_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
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
    mut v_t_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1535_);
    leanh::lean_dec_ref(v___y_1534_);
    leanh::lean_dec(v___y_1533_);
    leanh::lean_dec_ref(v___y_1532_);
    leanh::lean_dec(v___y_1531_);
    leanh::lean_dec_ref(v___y_1530_);
    leanh::lean_dec(v___y_1529_);
    leanh::lean_dec_ref(v___y_1528_);
    return v_res_1537_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(
    mut v_00_u03b1_1538_: *mut leanh::LeanObject,
    mut v_t_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
    mut v___y_1545_: *mut leanh::LeanObject,
    mut v___y_1546_: *mut leanh::LeanObject,
    mut v___y_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1550_: *mut leanh::LeanObject,
    mut v_t_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
    mut v___y_1557_: *mut leanh::LeanObject,
    mut v___y_1558_: *mut leanh::LeanObject,
    mut v___y_1559_: *mut leanh::LeanObject,
    mut v___y_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1559_);
    leanh::lean_dec_ref(v___y_1558_);
    leanh::lean_dec(v___y_1557_);
    leanh::lean_dec_ref(v___y_1556_);
    leanh::lean_dec(v___y_1555_);
    leanh::lean_dec_ref(v___y_1554_);
    leanh::lean_dec(v___y_1553_);
    leanh::lean_dec_ref(v___y_1552_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(
    mut v_stx_1562_: *mut leanh::LeanObject,
    mut v_act_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
    mut v___y_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
    mut v___y_1568_: *mut leanh::LeanObject,
    mut v___y_1569_: *mut leanh::LeanObject,
    mut v___y_1570_: *mut leanh::LeanObject,
    mut v___y_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1584_: u8 = 0;
    let mut v_cancelTk_x3f_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1586_: u8 = 0;
    let mut v_inheritedTraceOptions_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: u8 = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1573_ = leanh::lean_ctor_get(v___y_1570_, 0);
                v_fileMap_1574_ = leanh::lean_ctor_get(v___y_1570_, 1);
                v_options_1575_ = leanh::lean_ctor_get(v___y_1570_, 2);
                v_currRecDepth_1576_ = leanh::lean_ctor_get(v___y_1570_, 3);
                v_maxRecDepth_1577_ = leanh::lean_ctor_get(v___y_1570_, 4);
                v_currNamespace_1578_ = leanh::lean_ctor_get(v___y_1570_, 6);
                v_openDecls_1579_ = leanh::lean_ctor_get(v___y_1570_, 7);
                v_initHeartbeats_1580_ = leanh::lean_ctor_get(v___y_1570_, 8);
                v_maxHeartbeats_1581_ = leanh::lean_ctor_get(v___y_1570_, 9);
                v_quotContext_1582_ = leanh::lean_ctor_get(v___y_1570_, 10);
                v_currMacroScope_1583_ = leanh::lean_ctor_get(v___y_1570_, 11);
                v_diag_1584_ = leanh::lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1585_ = leanh::lean_ctor_get(v___y_1570_, 12);
                v_suppressElabErrors_1586_ = leanh::lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1587_ = leanh::lean_ctor_get(v___y_1570_, 13);
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
                leanh::lean_inc_ref(v_inheritedTraceOptions_1587_);
                leanh::lean_inc(v_cancelTk_x3f_1585_);
                leanh::lean_inc(v_currMacroScope_1583_);
                leanh::lean_inc(v_quotContext_1582_);
                leanh::lean_inc(v_maxHeartbeats_1581_);
                leanh::lean_inc(v_initHeartbeats_1580_);
                leanh::lean_inc(v_openDecls_1579_);
                leanh::lean_inc(v_currNamespace_1578_);
                leanh::lean_inc(v_maxRecDepth_1577_);
                leanh::lean_inc(v_currRecDepth_1576_);
                leanh::lean_inc_ref(v_options_1575_);
                leanh::lean_inc_ref(v_fileMap_1574_);
                leanh::lean_inc_ref(v_fileName_1573_);
                v___x_1590_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1590_, 0, v_fileName_1573_);
                leanh::lean_ctor_set(v___x_1590_, 1, v_fileMap_1574_);
                leanh::lean_ctor_set(v___x_1590_, 2, v_options_1575_);
                leanh::lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1576_);
                leanh::lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1577_);
                leanh::lean_ctor_set(v___x_1590_, 5, v_stx_1562_);
                leanh::lean_ctor_set(v___x_1590_, 6, v_currNamespace_1578_);
                leanh::lean_ctor_set(v___x_1590_, 7, v_openDecls_1579_);
                leanh::lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1580_);
                leanh::lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1581_);
                leanh::lean_ctor_set(v___x_1590_, 10, v_quotContext_1582_);
                leanh::lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1583_);
                leanh::lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1585_);
                leanh::lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1587_);
                leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_1584_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1589_,
                );
                leanh::lean_inc(v___y_1571_);
                leanh::lean_inc(v___y_1569_);
                leanh::lean_inc_ref(v___y_1568_);
                leanh::lean_inc(v___y_1567_);
                leanh::lean_inc_ref(v___y_1566_);
                leanh::lean_inc(v___y_1565_);
                leanh::lean_inc_ref(v___y_1564_);
                v___x_1591_ = leanh::lean_apply_9(
                    v_act_1563_,
                    v___y_1564_,
                    v___y_1565_,
                    v___y_1566_,
                    v___y_1567_,
                    v___y_1568_,
                    v___y_1569_,
                    v___x_1590_,
                    v___y_1571_,
                    leanh::lean_box(0),
                );
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_stx_1593_: *mut leanh::LeanObject,
    mut v_act_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1593_, v_act_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
    leanh::lean_dec(v___y_1602_);
    leanh::lean_dec_ref(v___y_1601_);
    leanh::lean_dec(v___y_1600_);
    leanh::lean_dec_ref(v___y_1599_);
    leanh::lean_dec(v___y_1598_);
    leanh::lean_dec_ref(v___y_1597_);
    leanh::lean_dec(v___y_1596_);
    leanh::lean_dec_ref(v___y_1595_);
    return v_res_1604_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(
    mut v_act_1605_: *mut leanh::LeanObject,
    mut v_snd_1606_: *mut leanh::LeanObject,
    mut v_____r_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_snd_1606_);
    v___x_1617_ = leanh::lean_apply_1(v_act_1605_, v_snd_1606_);
    v___x_1618_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_1606_, v___x_1617_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_act_1619_: *mut leanh::LeanObject,
    mut v_snd_1620_: *mut leanh::LeanObject,
    mut v_____r_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
    mut v___y_1627_: *mut leanh::LeanObject,
    mut v___y_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_1619_, v_snd_1620_, v_____r_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
    leanh::lean_dec(v___y_1629_);
    leanh::lean_dec_ref(v___y_1628_);
    leanh::lean_dec(v___y_1627_);
    leanh::lean_dec_ref(v___y_1626_);
    leanh::lean_dec(v___y_1625_);
    leanh::lean_dec_ref(v___y_1624_);
    leanh::lean_dec(v___y_1623_);
    leanh::lean_dec_ref(v___y_1622_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(
    mut v_val_1633_: *mut leanh::LeanObject,
    mut v___f_1634_: *mut leanh::LeanObject,
    mut v___y_1635_: *mut leanh::LeanObject,
    mut v___y_1636_: *mut leanh::LeanObject,
    mut v___y_1637_: *mut leanh::LeanObject,
    mut v___y_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tacSnap_x3f_1649_ = leanh::lean_ctor_get(v___y_1637_, 6);
                if leanh::lean_obj_tag(v_tacSnap_x3f_1649_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_1650_ = leanh::lean_ctor_get(v_tacSnap_x3f_1649_, 0);
                    v_old_x3f_1651_ = leanh::lean_ctor_get(v_val_1650_, 0);
                    if leanh::lean_obj_tag(v_old_x3f_1651_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_val_1633_);
                        v___x_1652_ = leanh::lean_box(0);
                        v___x_1653_ = leanh::lean_apply_10(
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
                            leanh::lean_box(0),
                        );
                        return v___x_1653_;
                    }
                }
            }
            1 => {
                v_val_1645_ = leanh::lean_ctor_get(v_val_1633_, 1);
                leanh::lean_inc(v_val_1645_);
                leanh::lean_dec_ref(v_val_1633_);
                v___x_1646_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0;
                v___x_1647_ =
                    l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_1646_, v_val_1645_);
                v___x_1648_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(
    mut v_val_1654_: *mut leanh::LeanObject,
    mut v___f_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_1654_, v___f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(
    mut v_split_1666_: *mut leanh::LeanObject,
    mut v_act_1667_: *mut leanh::LeanObject,
    mut v_stx_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1679_: u8 = 0;
    let mut v___y_1680_: u8 = 0;
    let mut v___y_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: u8 = 0;
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: u8 = 0;
    let mut v___y_1688_: u8 = 0;
    let mut v___y_1689_: u8 = 0;
    let mut v___y_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: u8 = 0;
    let mut v___y_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: u8 = 0;
    let mut v___y_1694_: u8 = 0;
    let mut v___y_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: u8 = 0;
    let mut v___y_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: u8 = 0;
    let mut v___y_1703_: u8 = 0;
    let mut v___y_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: u8 = 0;
    let mut v___y_1707_: u8 = 0;
    let mut v___y_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: u8 = 0;
    let mut v___y_1712_: u8 = 0;
    let mut v___y_1713_: u8 = 0;
    let mut v___y_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: u8 = 0;
    let mut v___y_1716_: u8 = 0;
    let mut v___y_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: u8 = 0;
    let mut v___y_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: u8 = 0;
    let mut v___y_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_1731_: u8 = 0;
    let mut v_errToSorry_1732_: u8 = 0;
    let mut v_autoBoundImplicitContext_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_1734_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_1737_: u8 = 0;
    let mut v_heedElabAsElim_1738_: u8 = 0;
    let mut v_isNoncomputableSection_1739_: u8 = 0;
    let mut v_isMetaSection_1740_: u8 = 0;
    let mut v_ignoreTCFailures_1741_: u8 = 0;
    let mut v_inPattern_1742_: u8 = 0;
    let mut v_tacSnap_x3f_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_1744_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_1745_: u8 = 0;
    let mut v_checkDeprecated_1746_: u8 = 0;
    let mut v_fixedTermElabs_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v___f_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_split_1666_);
                v___x_1725_ = leanh::lean_apply_1(v_split_1666_, v_stx_1668_);
                v_fst_1726_ = leanh::lean_ctor_get(v___x_1725_, 0);
                leanh::lean_inc(v_fst_1726_);
                v_snd_1727_ = leanh::lean_ctor_get(v___x_1725_, 1);
                leanh::lean_inc_n(v_snd_1727_, 2);
                leanh::lean_dec_ref(v___x_1725_);
                v_options_1728_ = leanh::lean_ctor_get(v___y_1675_, 2);
                v_declName_x3f_1729_ = leanh::lean_ctor_get(v___y_1671_, 0);
                v_macroStack_1730_ = leanh::lean_ctor_get(v___y_1671_, 1);
                v_mayPostpone_1731_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_1732_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_1733_ = leanh::lean_ctor_get(v___y_1671_, 2);
                v_autoBoundImplicitForbidden_1734_ = leanh::lean_ctor_get(v___y_1671_, 3);
                v_sectionVars_1735_ = leanh::lean_ctor_get(v___y_1671_, 4);
                v_sectionFVars_1736_ = leanh::lean_ctor_get(v___y_1671_, 5);
                v_implicitLambda_1737_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_1738_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_1739_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_1740_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_1741_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_1742_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_1743_ = leanh::lean_ctor_get(v___y_1671_, 6);
                v_saveRecAppSyntax_1744_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_1745_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_1746_ = leanh::lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_1747_ = leanh::lean_ctor_get(v___y_1671_, 7);
                leanh::lean_inc_ref(v_act_1667_);
                v___f_1770_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 2);
                leanh::lean_closure_set(v___f_1770_, 0, v_act_1667_);
                leanh::lean_closure_set(v___f_1770_, 1, v_snd_1727_);
                if leanh::lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    leanh::lean_dec_ref(v___f_1770_);
                    state = 6;
                    continue;
                } else {
                    v_val_1774_ = leanh::lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1775_ = leanh::lean_ctor_get(v_val_1774_, 0);
                    if leanh::lean_obj_tag(v_old_x3f_1775_) == 1 {
                        leanh::lean_dec(v_snd_1727_);
                        leanh::lean_dec_ref(v_act_1667_);
                        v_val_1776_ = leanh::lean_ctor_get(v_old_x3f_1775_, 0);
                        leanh::lean_inc(v_val_1776_);
                        v___f_1777_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
                        leanh::lean_closure_set(v___f_1777_, 0, v_val_1776_);
                        leanh::lean_closure_set(v___f_1777_, 1, v___f_1770_);
                        v___y_1749_ = v___f_1777_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_1770_);
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_1695_);
                leanh::lean_inc(v___y_1690_);
                leanh::lean_inc(v___y_1682_);
                leanh::lean_inc_ref(v___y_1686_);
                leanh::lean_inc(v___y_1681_);
                leanh::lean_inc(v___y_1685_);
                leanh::lean_inc(v___y_1696_);
                v___x_1699_ = leanh::lean_alloc_ctor(0, 8, (11) as u32);
                leanh::lean_ctor_set(v___x_1699_, 0, v___y_1696_);
                leanh::lean_ctor_set(v___x_1699_, 1, v___y_1685_);
                leanh::lean_ctor_set(v___x_1699_, 2, v___y_1681_);
                leanh::lean_ctor_set(v___x_1699_, 3, v___y_1686_);
                leanh::lean_ctor_set(v___x_1699_, 4, v___y_1682_);
                leanh::lean_ctor_set(v___x_1699_, 5, v___y_1690_);
                leanh::lean_ctor_set(v___x_1699_, 6, v___y_1698_);
                leanh::lean_ctor_set(v___x_1699_, 7, v___y_1695_);
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    v___y_1680_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    v___y_1687_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    v___y_1697_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    v___y_1684_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                    v___y_1688_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                    v___y_1694_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                    v___y_1691_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                    v___y_1679_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                    v___y_1693_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                    v___y_1683_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                    v___y_1689_,
                );
                leanh::lean_inc(v___y_1676_);
                leanh::lean_inc_ref(v___y_1675_);
                leanh::lean_inc(v___y_1674_);
                leanh::lean_inc_ref(v___y_1673_);
                leanh::lean_inc(v___y_1672_);
                leanh::lean_inc(v___y_1670_);
                leanh::lean_inc_ref(v___y_1669_);
                v___x_1700_ = leanh::lean_apply_9(
                    v___y_1692_,
                    v___y_1669_,
                    v___y_1670_,
                    v___x_1699_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                    v___y_1675_,
                    v___y_1676_,
                    leanh::lean_box(0),
                );
                return v___x_1700_;
            }
            2 => {
                v___x_1723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1723_, 0, v___y_1722_);
                leanh::lean_ctor_set(v___x_1723_, 1, v_new_1709_);
                v___x_1724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1724_, 0, v___x_1723_);
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
                if leanh::lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    leanh::lean_dec(v_fst_1726_);
                    leanh::lean_dec_ref(v_split_1666_);
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
                    v_val_1750_ = leanh::lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1751_ = leanh::lean_ctor_get(v_val_1750_, 0);
                    if leanh::lean_obj_tag(v_old_x3f_1751_) == 0 {
                        leanh::lean_dec(v_fst_1726_);
                        leanh::lean_dec_ref(v_split_1666_);
                        v_new_1752_ = leanh::lean_ctor_get(v_val_1750_, 1);
                        leanh::lean_inc(v_new_1752_);
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
                        v_val_1753_ = leanh::lean_ctor_get(v_old_x3f_1751_, 0);
                        v_new_1754_ = leanh::lean_ctor_get(v_val_1750_, 1);
                        v_stx_1755_ = leanh::lean_ctor_get(v_val_1753_, 0);
                        v_val_1756_ = leanh::lean_ctor_get(v_val_1753_, 1);
                        leanh::lean_inc(v_stx_1755_);
                        v___x_1757_ = leanh::lean_apply_1(v_split_1666_, v_stx_1755_);
                        v_fst_1758_ = leanh::lean_ctor_get(v___x_1757_, 0);
                        v_snd_1759_ = leanh::lean_ctor_get(v___x_1757_, 1);
                        v_isSharedCheck_1769_ =
                            (!leanh::lean_is_exclusive(v___x_1757_)) as u8;
                        if v_isSharedCheck_1769_ == 0 {
                            v___x_1761_ = v___x_1757_;
                            v_isShared_1762_ = v_isSharedCheck_1769_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1759_);
                            leanh::lean_inc(v_fst_1758_);
                            leanh::lean_dec(v___x_1757_);
                            v___x_1761_ = leanh::lean_box(0);
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
                    leanh::lean_del_object(v___x_1761_);
                    leanh::lean_dec(v_snd_1759_);
                    v___x_1764_ = leanh::lean_box(0);
                    leanh::lean_inc(v_new_1754_);
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
                    leanh::lean_inc(v_val_1756_);
                    if v_isShared_1762_ == 0 {
                        leanh::lean_ctor_set(v___x_1761_, 1, v_val_1756_);
                        leanh::lean_ctor_set(v___x_1761_, 0, v_snd_1759_);
                        v___x_1766_ = v___x_1761_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_snd_1759_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_val_1756_);
                        v___x_1766_ = v_reuseFailAlloc_1768_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
                leanh::lean_inc(v_new_1754_);
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
                v___x_1772_ = leanh::lean_box(0);
                v___x_1773_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 3);
                leanh::lean_closure_set(v___x_1773_, 0, v_act_1667_);
                leanh::lean_closure_set(v___x_1773_, 1, v_snd_1727_);
                leanh::lean_closure_set(v___x_1773_, 2, v___x_1772_);
                v___y_1749_ = v___x_1773_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(
    mut v_split_1778_: *mut leanh::LeanObject,
    mut v_act_1779_: *mut leanh::LeanObject,
    mut v_stx_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
    mut v___y_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
    mut v___y_1789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1790_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1778_, v_act_1779_, v_stx_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
    leanh::lean_dec(v___y_1788_);
    leanh::lean_dec_ref(v___y_1787_);
    leanh::lean_dec(v___y_1786_);
    leanh::lean_dec_ref(v___y_1785_);
    leanh::lean_dec(v___y_1784_);
    leanh::lean_dec_ref(v___y_1783_);
    leanh::lean_dec(v___y_1782_);
    leanh::lean_dec_ref(v___y_1781_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(
    mut v_argIdx_1794_: *mut leanh::LeanObject,
    mut v_stx_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Syntax_getArgs(v_stx_1795_);
    v___x_1797_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_argIdx_1794_);
    v___x_1798_ = l_Array_toSubarray___redArg(v___x_1796_, v___x_1797_, v_argIdx_1794_);
    v___x_1799_ = l_Subarray_copy___redArg(v___x_1798_);
    v___x_1800_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1;
    v___x_1801_ = leanh::lean_box(2);
    v___x_1802_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    leanh::lean_ctor_set(v___x_1802_, 1, v___x_1800_);
    leanh::lean_ctor_set(v___x_1802_, 2, v___x_1799_);
    v___x_1803_ = l_Lean_Syntax_getArg(v_stx_1795_, v_argIdx_1794_);
    leanh::lean_dec(v_argIdx_1794_);
    v___x_1804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1804_, 0, v___x_1802_);
    leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(
    mut v_argIdx_1805_: *mut leanh::LeanObject,
    mut v_stx_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_1805_, v_stx_1806_);
    leanh::lean_dec(v_stx_1806_);
    return v_res_1807_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(
    mut v_argIdx_1808_: *mut leanh::LeanObject,
    mut v_act_1809_: *mut leanh::LeanObject,
    mut v_stx_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1820_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_1820_, 0, v_argIdx_1808_);
    v___x_1821_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_1820_, v_act_1809_, v_stx_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(
    mut v_argIdx_1822_: *mut leanh::LeanObject,
    mut v_act_1823_: *mut leanh::LeanObject,
    mut v_stx_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
    mut v___y_1830_: *mut leanh::LeanObject,
    mut v___y_1831_: *mut leanh::LeanObject,
    mut v___y_1832_: *mut leanh::LeanObject,
    mut v___y_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1822_, v_act_1823_, v_stx_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    leanh::lean_dec(v___y_1832_);
    leanh::lean_dec_ref(v___y_1831_);
    leanh::lean_dec(v___y_1830_);
    leanh::lean_dec_ref(v___y_1829_);
    leanh::lean_dec(v___y_1828_);
    leanh::lean_dec_ref(v___y_1827_);
    leanh::lean_dec(v___y_1826_);
    leanh::lean_dec_ref(v___y_1825_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(
    mut v_00_u03b1_1835_: *mut leanh::LeanObject,
    mut v_argIdx_1836_: *mut leanh::LeanObject,
    mut v_act_1837_: *mut leanh::LeanObject,
    mut v_stx_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1836_, v_act_1837_, v_stx_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    return v___x_1848_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_argIdx_1850_: *mut leanh::LeanObject,
    mut v_act_1851_: *mut leanh::LeanObject,
    mut v_stx_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1860_);
    leanh::lean_dec_ref(v___y_1859_);
    leanh::lean_dec(v___y_1858_);
    leanh::lean_dec_ref(v___y_1857_);
    leanh::lean_dec(v___y_1856_);
    leanh::lean_dec_ref(v___y_1855_);
    leanh::lean_dec(v___y_1854_);
    leanh::lean_dec_ref(v___y_1853_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(
    mut v___y_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = lean_st_ref_get(v___y_1865_);
    v_env_1868_ = leanh::lean_ctor_get(v___x_1867_, 0);
    leanh::lean_inc_ref(v_env_1868_);
    leanh::lean_dec(v___x_1867_);
    v___x_1869_ = lean_st_ref_get(v___y_1863_);
    v_mctx_1870_ = leanh::lean_ctor_get(v___x_1869_, 0);
    leanh::lean_inc_ref(v_mctx_1870_);
    leanh::lean_dec(v___x_1869_);
    v_options_1871_ = leanh::lean_ctor_get(v___y_1864_, 2);
    v_currNamespace_1872_ = leanh::lean_ctor_get(v___y_1864_, 6);
    v_openDecls_1873_ = leanh::lean_ctor_get(v___y_1864_, 7);
    v___x_1874_ = lean_st_ref_get(v___y_1865_);
    v_ngen_1875_ = leanh::lean_ctor_get(v___x_1874_, 2);
    leanh::lean_inc_ref(v_ngen_1875_);
    leanh::lean_dec(v___x_1874_);
    v___x_1876_ = leanh::lean_box(0);
    v___x_1877_ = l_Lean_instInhabitedFileMap_default;
    leanh::lean_inc(v_openDecls_1873_);
    leanh::lean_inc(v_currNamespace_1872_);
    leanh::lean_inc_ref(v_options_1871_);
    v___x_1878_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_1878_, 0, v_env_1868_);
    leanh::lean_ctor_set(v___x_1878_, 1, v___x_1876_);
    leanh::lean_ctor_set(v___x_1878_, 2, v___x_1877_);
    leanh::lean_ctor_set(v___x_1878_, 3, v_mctx_1870_);
    leanh::lean_ctor_set(v___x_1878_, 4, v_options_1871_);
    leanh::lean_ctor_set(v___x_1878_, 5, v_currNamespace_1872_);
    leanh::lean_ctor_set(v___x_1878_, 6, v_openDecls_1873_);
    leanh::lean_ctor_set(v___x_1878_, 7, v_ngen_1875_);
    v___x_1879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1880_, v___y_1881_, v___y_1882_);
    leanh::lean_dec(v___y_1882_);
    leanh::lean_dec_ref(v___y_1881_);
    leanh::lean_dec(v___y_1880_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1894_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1890_, v___y_1891_, v___y_1892_);
                v_a_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                v_isSharedCheck_1919_ = (!leanh::lean_is_exclusive(v___x_1894_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1897_ = v___x_1894_;
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1895_);
                    leanh::lean_dec(v___x_1894_);
                    v___x_1897_ = leanh::lean_box(0);
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1899_ = leanh::lean_ctor_get(v___y_1891_, 1);
                v_env_1900_ = leanh::lean_ctor_get(v_a_1895_, 0);
                v_mctx_1901_ = leanh::lean_ctor_get(v_a_1895_, 3);
                v_options_1902_ = leanh::lean_ctor_get(v_a_1895_, 4);
                v_currNamespace_1903_ = leanh::lean_ctor_get(v_a_1895_, 5);
                v_openDecls_1904_ = leanh::lean_ctor_get(v_a_1895_, 6);
                v_ngen_1905_ = leanh::lean_ctor_get(v_a_1895_, 7);
                v_isSharedCheck_1916_ = (!leanh::lean_is_exclusive(v_a_1895_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v_unused_1917_ = leanh::lean_ctor_get(v_a_1895_, 2);
                    leanh::lean_dec(v_unused_1917_);
                    v_unused_1918_ = leanh::lean_ctor_get(v_a_1895_, 1);
                    leanh::lean_dec(v_unused_1918_);
                    v___x_1907_ = v_a_1895_;
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ngen_1905_);
                    leanh::lean_inc(v_openDecls_1904_);
                    leanh::lean_inc(v_currNamespace_1903_);
                    leanh::lean_inc(v_options_1902_);
                    leanh::lean_inc(v_mctx_1901_);
                    leanh::lean_inc(v_env_1900_);
                    leanh::lean_dec(v_a_1895_);
                    v___x_1907_ = leanh::lean_box(0);
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1909_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_fileMap_1899_);
                if v_isShared_1908_ == 0 {
                    leanh::lean_ctor_set(v___x_1907_, 2, v_fileMap_1899_);
                    leanh::lean_ctor_set(v___x_1907_, 1, v___x_1909_);
                    v___x_1911_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_env_1900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_fileMap_1899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_mctx_1901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_options_1902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_currNamespace_1903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_openDecls_1904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_ngen_1905_);
                    v___x_1911_ = v_reuseFailAlloc_1915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1898_ == 0 {
                    leanh::lean_ctor_set(v___x_1897_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
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
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
    leanh::lean_dec(v___y_1927_);
    leanh::lean_dec_ref(v___y_1926_);
    leanh::lean_dec(v___y_1925_);
    leanh::lean_dec_ref(v___y_1924_);
    leanh::lean_dec(v___y_1923_);
    leanh::lean_dec_ref(v___y_1922_);
    leanh::lean_dec(v___y_1921_);
    leanh::lean_dec_ref(v___y_1920_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
    mut v___y_1935_: *mut leanh::LeanObject,
    mut v___y_1936_: *mut leanh::LeanObject,
    mut v___y_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1939_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
                v_a_1940_ = leanh::lean_ctor_get(v___x_1939_, 0);
                v_isSharedCheck_1949_ = (!leanh::lean_is_exclusive(v___x_1939_)) as u8;
                if v_isSharedCheck_1949_ == 0 {
                    v___x_1942_ = v___x_1939_;
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1940_);
                    leanh::lean_dec(v___x_1939_);
                    v___x_1942_ = leanh::lean_box(0);
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1944_, 0, v_a_1940_);
                v___x_1945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1945_, 0, v___x_1944_);
                if v_isShared_1943_ == 0 {
                    leanh::lean_ctor_set(v___x_1942_, 0, v___x_1945_);
                    v___x_1947_ = v___x_1942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
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
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
    leanh::lean_dec(v___y_1957_);
    leanh::lean_dec_ref(v___y_1956_);
    leanh::lean_dec(v___y_1955_);
    leanh::lean_dec_ref(v___y_1954_);
    leanh::lean_dec(v___y_1953_);
    leanh::lean_dec_ref(v___y_1952_);
    leanh::lean_dec(v___y_1951_);
    leanh::lean_dec_ref(v___y_1950_);
    return v_res_1959_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = leanh::lean_unsigned_to_nat(32);
    v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
    v___x_1962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = 5usize;
    v___x_1964_ = leanh::lean_unsigned_to_nat(0);
    v___x_1965_ = leanh::lean_unsigned_to_nat(32);
    v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
    v___x_1967_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
    v___x_1968_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    leanh::lean_ctor_set(v___x_1968_, 1, v___x_1966_);
    leanh::lean_ctor_set(v___x_1968_, 2, v___x_1964_);
    leanh::lean_ctor_set(v___x_1968_, 3, v___x_1964_);
    leanh::lean_ctor_set_usize(v___x_1968_, 4, v___x_1963_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(
    mut v___y_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v_enabled_1987_: u8 = 0;
    let mut v_assignment_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1971_ = lean_st_ref_get(v___y_1969_);
                v_infoState_1972_ = leanh::lean_ctor_get(v___x_1971_, 7);
                leanh::lean_inc_ref(v_infoState_1972_);
                leanh::lean_dec(v___x_1971_);
                v_trees_1973_ = leanh::lean_ctor_get(v_infoState_1972_, 2);
                leanh::lean_inc_ref(v_trees_1973_);
                leanh::lean_dec_ref(v_infoState_1972_);
                v___x_1974_ = lean_st_ref_take(v___y_1969_);
                v_infoState_1975_ = leanh::lean_ctor_get(v___x_1974_, 7);
                v_env_1976_ = leanh::lean_ctor_get(v___x_1974_, 0);
                v_nextMacroScope_1977_ = leanh::lean_ctor_get(v___x_1974_, 1);
                v_ngen_1978_ = leanh::lean_ctor_get(v___x_1974_, 2);
                v_auxDeclNGen_1979_ = leanh::lean_ctor_get(v___x_1974_, 3);
                v_traceState_1980_ = leanh::lean_ctor_get(v___x_1974_, 4);
                v_cache_1981_ = leanh::lean_ctor_get(v___x_1974_, 5);
                v_messages_1982_ = leanh::lean_ctor_get(v___x_1974_, 6);
                v_snapshotTasks_1983_ = leanh::lean_ctor_get(v___x_1974_, 8);
                v_isSharedCheck_2004_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1985_ = v___x_1974_;
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1983_);
                    leanh::lean_inc(v_infoState_1975_);
                    leanh::lean_inc(v_messages_1982_);
                    leanh::lean_inc(v_cache_1981_);
                    leanh::lean_inc(v_traceState_1980_);
                    leanh::lean_inc(v_auxDeclNGen_1979_);
                    leanh::lean_inc(v_ngen_1978_);
                    leanh::lean_inc(v_nextMacroScope_1977_);
                    leanh::lean_inc(v_env_1976_);
                    leanh::lean_dec(v___x_1974_);
                    v___x_1985_ = leanh::lean_box(0);
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1987_ = leanh::lean_ctor_get_uint8(
                    v_infoState_1975_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1988_ = leanh::lean_ctor_get(v_infoState_1975_, 0);
                v_lazyAssignment_1989_ = leanh::lean_ctor_get(v_infoState_1975_, 1);
                v_isSharedCheck_2002_ = (!leanh::lean_is_exclusive(v_infoState_1975_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = leanh::lean_ctor_get(v_infoState_1975_, 2);
                    leanh::lean_dec(v_unused_2003_);
                    v___x_1991_ = v_infoState_1975_;
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_1989_);
                    leanh::lean_inc(v_assignment_1988_);
                    leanh::lean_dec(v_infoState_1975_);
                    v___x_1991_ = leanh::lean_box(0);
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1993_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
                if v_isShared_1992_ == 0 {
                    leanh::lean_ctor_set(v___x_1991_, 2, v___x_1993_);
                    v___x_1995_ = v___x_1991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_assignment_1988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_lazyAssignment_1989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 2, v___x_1993_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2001_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_1987_,
                    );
                    v___x_1995_ = v_reuseFailAlloc_2001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1986_ == 0 {
                    leanh::lean_ctor_set(v___x_1985_, 7, v___x_1995_);
                    v___x_1997_ = v___x_1985_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_env_1976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_nextMacroScope_1977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_ngen_1978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_auxDeclNGen_1979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_traceState_1980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 5, v_cache_1981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 6, v_messages_1982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 7, v___x_1995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 8, v_snapshotTasks_1983_);
                    v___x_1997_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1998_ = lean_st_ref_set(v___y_1969_, v___x_1997_);
                v___x_1999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1999_, 0, v_trees_1973_);
                return v___x_1999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2005_);
    leanh::lean_dec(v___y_2005_);
    return v_res_2007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(
    mut v___x_2008_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2009_: *mut leanh::LeanObject,
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_bs_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: usize = 0;
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2022_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2022_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_2009_);
                    v___x_2023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2023_, 0, v_bs_2012_);
                    return v___x_2023_;
                } else {
                    v_assignment_2024_ = leanh::lean_ctor_get(v___x_2008_, 0);
                    leanh::lean_inc_ref(v_ctx_x3f_2009_);
                    leanh::lean_inc(v___y_2020_);
                    leanh::lean_inc_ref(v___y_2019_);
                    leanh::lean_inc(v___y_2018_);
                    leanh::lean_inc_ref(v___y_2017_);
                    leanh::lean_inc(v___y_2016_);
                    leanh::lean_inc_ref(v___y_2015_);
                    leanh::lean_inc(v___y_2014_);
                    leanh::lean_inc_ref(v___y_2013_);
                    v___x_2025_ = leanh::lean_apply_9(
                        v_ctx_x3f_2009_,
                        v___y_2013_,
                        v___y_2014_,
                        v___y_2015_,
                        v___y_2016_,
                        v___y_2017_,
                        v___y_2018_,
                        v___y_2019_,
                        v___y_2020_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2025_) == 0 {
                        v_a_2026_ = leanh::lean_ctor_get(v___x_2025_, 0);
                        leanh::lean_inc(v_a_2026_);
                        leanh::lean_dec_ref_known(v___x_2025_, 1);
                        v_v_2027_ = lean_array_uget(v_bs_2012_, v_i_2011_);
                        v___x_2028_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2029_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2028_);
                        v_tree_2036_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_2027_, v_assignment_2024_);
                        if leanh::lean_obj_tag(v_a_2026_) == 0 {
                            v_a_2031_ = v_tree_2036_;
                            state = 1;
                            continue;
                        } else {
                            v_val_2037_ = leanh::lean_ctor_get(v_a_2026_, 0);
                            leanh::lean_inc(v_val_2037_);
                            leanh::lean_dec_ref_known(v_a_2026_, 1);
                            v___x_2038_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2038_, 0, v_val_2037_);
                            leanh::lean_ctor_set(v___x_2038_, 1, v_tree_2036_);
                            v_a_2031_ = v___x_2038_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_2012_);
                        leanh::lean_dec_ref(v_ctx_x3f_2009_);
                        v_a_2039_ = leanh::lean_ctor_get(v___x_2025_, 0);
                        v_isSharedCheck_2046_ =
                            (!leanh::lean_is_exclusive(v___x_2025_)) as u8;
                        if v_isSharedCheck_2046_ == 0 {
                            v___x_2041_ = v___x_2025_;
                            v_isShared_2042_ = v_isSharedCheck_2046_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2039_);
                            leanh::lean_dec(v___x_2025_);
                            v___x_2041_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
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
    mut v___x_2047_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2048_: *mut leanh::LeanObject,
    mut v_sz_2049_: *mut leanh::LeanObject,
    mut v_i_2050_: *mut leanh::LeanObject,
    mut v_bs_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
    mut v___y_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2061_: usize = 0;
    let mut v_i_boxed_2062_: usize = 0;
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2061_ = leanh::lean_unbox_usize(v_sz_2049_);
    leanh::lean_dec(v_sz_2049_);
    v_i_boxed_2062_ = leanh::lean_unbox_usize(v_i_2050_);
    leanh::lean_dec(v_i_2050_);
    v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2047_, v_ctx_x3f_2048_, v_sz_boxed_2061_, v_i_boxed_2062_, v_bs_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
    leanh::lean_dec(v___y_2059_);
    leanh::lean_dec_ref(v___y_2058_);
    leanh::lean_dec(v___y_2057_);
    leanh::lean_dec_ref(v___y_2056_);
    leanh::lean_dec(v___y_2055_);
    leanh::lean_dec_ref(v___y_2054_);
    leanh::lean_dec(v___y_2053_);
    leanh::lean_dec_ref(v___y_2052_);
    leanh::lean_dec_ref(v___x_2047_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(
    mut v___x_2064_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2065_: *mut leanh::LeanObject,
    mut v_x_2066_: *mut leanh::LeanObject,
    mut v___y_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
    mut v___y_2073_: *mut leanh::LeanObject,
    mut v___y_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v_sz_2080_: usize = 0;
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_a_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_vs_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_sz_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_a_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2066_) == 0 {
                    v_cs_2076_ = leanh::lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2102_ = (!leanh::lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2102_ == 0 {
                        v___x_2078_ = v_x_2066_;
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_2076_);
                        leanh::lean_dec(v_x_2066_);
                        v___x_2078_ = leanh::lean_box(0);
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2103_ = leanh::lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2129_ = (!leanh::lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2105_ = v_x_2066_;
                        v_isShared_2106_ = v_isSharedCheck_2129_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2103_);
                        leanh::lean_dec(v_x_2066_);
                        v___x_2105_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_2082_) == 0 {
                    v_a_2083_ = leanh::lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2093_ = (!leanh::lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2093_ == 0 {
                        v___x_2085_ = v___x_2082_;
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2083_);
                        leanh::lean_dec(v___x_2082_);
                        v___x_2085_ = leanh::lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2078_);
                    v_a_2094_ = leanh::lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2101_ = (!leanh::lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2096_ = v___x_2082_;
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2094_);
                        leanh::lean_dec(v___x_2082_);
                        v___x_2096_ = leanh::lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2079_ == 0 {
                    leanh::lean_ctor_set(v___x_2078_, 0, v_a_2083_);
                    v___x_2088_ = v___x_2078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2083_);
                    v___x_2088_ = v_reuseFailAlloc_2092_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2086_ == 0 {
                    leanh::lean_ctor_set(v___x_2085_, 0, v___x_2088_);
                    v___x_2090_ = v___x_2085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
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
                    v_reuseFailAlloc_2100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
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
                if leanh::lean_obj_tag(v___x_2109_) == 0 {
                    v_a_2110_ = leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2120_ = (!leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2120_ == 0 {
                        v___x_2112_ = v___x_2109_;
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2110_);
                        leanh::lean_dec(v___x_2109_);
                        v___x_2112_ = leanh::lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2105_);
                    v_a_2121_ = leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2128_ = (!leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2128_ == 0 {
                        v___x_2123_ = v___x_2109_;
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2121_);
                        leanh::lean_dec(v___x_2109_);
                        v___x_2123_ = leanh::lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2106_ == 0 {
                    leanh::lean_ctor_set(v___x_2105_, 0, v_a_2110_);
                    v___x_2115_ = v___x_2105_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2119_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2113_ == 0 {
                    leanh::lean_ctor_set(v___x_2112_, 0, v___x_2115_);
                    v___x_2117_ = v___x_2112_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
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
                    v_reuseFailAlloc_2127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
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
    mut v___x_2130_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2131_: *mut leanh::LeanObject,
    mut v_sz_2132_: usize,
    mut v_i_2133_: usize,
    mut v_bs_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2144_ = lean_usize_dec_lt(v_i_2133_, v_sz_2132_);
                if v___x_2144_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_2131_);
                    v___x_2145_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2145_, 0, v_bs_2134_);
                    return v___x_2145_;
                } else {
                    v_v_2146_ = lean_array_uget_borrowed(v_bs_2134_, v_i_2133_);
                    leanh::lean_inc(v_v_2146_);
                    leanh::lean_inc_ref(v_ctx_x3f_2131_);
                    v___x_2147_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2130_, v_ctx_x3f_2131_, v_v_2146_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
                    if leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = leanh::lean_ctor_get(v___x_2147_, 0);
                        leanh::lean_inc(v_a_2148_);
                        leanh::lean_dec_ref_known(v___x_2147_, 1);
                        v___x_2149_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2150_ = lean_array_uset(v_bs_2134_, v_i_2133_, v___x_2149_);
                        v___x_2151_ = 1usize;
                        v___x_2152_ = lean_usize_add(v_i_2133_, v___x_2151_);
                        v___x_2153_ = lean_array_uset(v_bs_x27_2150_, v_i_2133_, v_a_2148_);
                        v_i_2133_ = v___x_2152_;
                        v_bs_2134_ = v___x_2153_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_2134_);
                        leanh::lean_dec_ref(v_ctx_x3f_2131_);
                        v_a_2155_ = leanh::lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2162_ =
                            (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2147_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2155_);
                            leanh::lean_dec(v___x_2147_);
                            v___x_2157_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2161_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
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
    mut v___x_2163_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2164_: *mut leanh::LeanObject,
    mut v_sz_2165_: *mut leanh::LeanObject,
    mut v_i_2166_: *mut leanh::LeanObject,
    mut v_bs_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
    mut v___y_2173_: *mut leanh::LeanObject,
    mut v___y_2174_: *mut leanh::LeanObject,
    mut v___y_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2177_: usize = 0;
    let mut v_i_boxed_2178_: usize = 0;
    let mut v_res_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2177_ = leanh::lean_unbox_usize(v_sz_2165_);
    leanh::lean_dec(v_sz_2165_);
    v_i_boxed_2178_ = leanh::lean_unbox_usize(v_i_2166_);
    leanh::lean_dec(v_i_2166_);
    v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_2163_, v_ctx_x3f_2164_, v_sz_boxed_2177_, v_i_boxed_2178_, v_bs_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
    leanh::lean_dec(v___y_2175_);
    leanh::lean_dec_ref(v___y_2174_);
    leanh::lean_dec(v___y_2173_);
    leanh::lean_dec_ref(v___y_2172_);
    leanh::lean_dec(v___y_2171_);
    leanh::lean_dec_ref(v___y_2170_);
    leanh::lean_dec(v___y_2169_);
    leanh::lean_dec_ref(v___y_2168_);
    leanh::lean_dec_ref(v___x_2163_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(
    mut v___x_2180_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2181_: *mut leanh::LeanObject,
    mut v_x_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v___y_2191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2192_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2180_, v_ctx_x3f_2181_, v_x_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
    leanh::lean_dec(v___y_2190_);
    leanh::lean_dec_ref(v___y_2189_);
    leanh::lean_dec(v___y_2188_);
    leanh::lean_dec_ref(v___y_2187_);
    leanh::lean_dec(v___y_2186_);
    leanh::lean_dec_ref(v___y_2185_);
    leanh::lean_dec(v___y_2184_);
    leanh::lean_dec_ref(v___y_2183_);
    leanh::lean_dec_ref(v___x_2180_);
    return v_res_2192_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(
    mut v___x_2193_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2194_: *mut leanh::LeanObject,
    mut v_t_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
    mut v___y_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
    mut v___y_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_2208_: usize = 0;
    let mut v_tailOff_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2215_: usize = 0;
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_a_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_a_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2205_ = leanh::lean_ctor_get(v_t_2195_, 0);
                v_tail_2206_ = leanh::lean_ctor_get(v_t_2195_, 1);
                v_size_2207_ = leanh::lean_ctor_get(v_t_2195_, 2);
                v_shift_2208_ = leanh::lean_ctor_get_usize(v_t_2195_, 4);
                v_tailOff_2209_ = leanh::lean_ctor_get(v_t_2195_, 3);
                v_isSharedCheck_2245_ = (!leanh::lean_is_exclusive(v_t_2195_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v___x_2211_ = v_t_2195_;
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_2209_);
                    leanh::lean_inc(v_size_2207_);
                    leanh::lean_inc(v_tail_2206_);
                    leanh::lean_inc(v_root_2205_);
                    leanh::lean_dec(v_t_2195_);
                    v___x_2211_ = leanh::lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_ctx_x3f_2194_);
                v___x_2213_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2193_, v_ctx_x3f_2194_, v_root_2205_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                if leanh::lean_obj_tag(v___x_2213_) == 0 {
                    v_a_2214_ = leanh::lean_ctor_get(v___x_2213_, 0);
                    leanh::lean_inc(v_a_2214_);
                    leanh::lean_dec_ref_known(v___x_2213_, 1);
                    v_sz_2215_ = lean_array_size(v_tail_2206_);
                    v___x_2216_ = 0usize;
                    v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2193_, v_ctx_x3f_2194_, v_sz_2215_, v___x_2216_, v_tail_2206_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                    if leanh::lean_obj_tag(v___x_2217_) == 0 {
                        v_a_2218_ = leanh::lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2228_ =
                            (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2228_ == 0 {
                            v___x_2220_ = v___x_2217_;
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2218_);
                            leanh::lean_dec(v___x_2217_);
                            v___x_2220_ = leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2214_);
                        leanh::lean_del_object(v___x_2211_);
                        leanh::lean_dec(v_tailOff_2209_);
                        leanh::lean_dec(v_size_2207_);
                        v_a_2229_ = leanh::lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2236_ =
                            (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2236_ == 0 {
                            v___x_2231_ = v___x_2217_;
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2229_);
                            leanh::lean_dec(v___x_2217_);
                            v___x_2231_ = leanh::lean_box(0);
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2211_);
                    leanh::lean_dec(v_tailOff_2209_);
                    leanh::lean_dec(v_size_2207_);
                    leanh::lean_dec_ref(v_tail_2206_);
                    leanh::lean_dec_ref(v_ctx_x3f_2194_);
                    v_a_2237_ = leanh::lean_ctor_get(v___x_2213_, 0);
                    v_isSharedCheck_2244_ = (!leanh::lean_is_exclusive(v___x_2213_)) as u8;
                    if v_isSharedCheck_2244_ == 0 {
                        v___x_2239_ = v___x_2213_;
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2237_);
                        leanh::lean_dec(v___x_2213_);
                        v___x_2239_ = leanh::lean_box(0);
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2212_ == 0 {
                    leanh::lean_ctor_set(v___x_2211_, 1, v_a_2218_);
                    leanh::lean_ctor_set(v___x_2211_, 0, v_a_2214_);
                    v___x_2223_ = v___x_2211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_size_2207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_tailOff_2209_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_2227_, 4, v_shift_2208_);
                    v___x_2223_ = v_reuseFailAlloc_2227_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2221_ == 0 {
                    leanh::lean_ctor_set(v___x_2220_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
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
                    v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
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
                    v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
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
    mut v___x_2246_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2247_: *mut leanh::LeanObject,
    mut v_t_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_2246_, v_ctx_x3f_2247_, v_t_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
    leanh::lean_dec(v___y_2256_);
    leanh::lean_dec_ref(v___y_2255_);
    leanh::lean_dec(v___y_2254_);
    leanh::lean_dec_ref(v___y_2253_);
    leanh::lean_dec(v___y_2252_);
    leanh::lean_dec_ref(v___y_2251_);
    leanh::lean_dec(v___y_2250_);
    leanh::lean_dec_ref(v___y_2249_);
    leanh::lean_dec_ref(v___x_2246_);
    return v_res_2258_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(
    mut v___y_2259_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2260_: *mut leanh::LeanObject,
    mut v___y_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
    mut v___y_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
    mut v_a_x3f_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_enabled_2292_: u8 = 0;
    let mut v_assignment_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_a_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2271_ = lean_st_ref_get(v___y_2259_);
                v_infoState_2272_ = leanh::lean_ctor_get(v___x_2271_, 7);
                leanh::lean_inc_ref(v_infoState_2272_);
                leanh::lean_dec(v___x_2271_);
                v_trees_2273_ = leanh::lean_ctor_get(v_infoState_2272_, 2);
                leanh::lean_inc_ref(v_trees_2273_);
                v___x_2274_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_2272_, v_ctx_x3f_2260_, v_trees_2273_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2259_);
                leanh::lean_dec_ref(v_infoState_2272_);
                if leanh::lean_obj_tag(v___x_2274_) == 0 {
                    v_a_2275_ = leanh::lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2313_ = (!leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2313_ == 0 {
                        v___x_2277_ = v___x_2274_;
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2275_);
                        leanh::lean_dec(v___x_2274_);
                        v___x_2277_ = leanh::lean_box(0);
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_2268_);
                    v_a_2314_ = leanh::lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2321_ = (!leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2274_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2314_);
                        leanh::lean_dec(v___x_2274_);
                        v___x_2316_ = leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2279_ = lean_st_ref_take(v___y_2259_);
                v_infoState_2280_ = leanh::lean_ctor_get(v___x_2279_, 7);
                v_env_2281_ = leanh::lean_ctor_get(v___x_2279_, 0);
                v_nextMacroScope_2282_ = leanh::lean_ctor_get(v___x_2279_, 1);
                v_ngen_2283_ = leanh::lean_ctor_get(v___x_2279_, 2);
                v_auxDeclNGen_2284_ = leanh::lean_ctor_get(v___x_2279_, 3);
                v_traceState_2285_ = leanh::lean_ctor_get(v___x_2279_, 4);
                v_cache_2286_ = leanh::lean_ctor_get(v___x_2279_, 5);
                v_messages_2287_ = leanh::lean_ctor_get(v___x_2279_, 6);
                v_snapshotTasks_2288_ = leanh::lean_ctor_get(v___x_2279_, 8);
                v_isSharedCheck_2312_ = (!leanh::lean_is_exclusive(v___x_2279_)) as u8;
                if v_isSharedCheck_2312_ == 0 {
                    v___x_2290_ = v___x_2279_;
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2288_);
                    leanh::lean_inc(v_infoState_2280_);
                    leanh::lean_inc(v_messages_2287_);
                    leanh::lean_inc(v_cache_2286_);
                    leanh::lean_inc(v_traceState_2285_);
                    leanh::lean_inc(v_auxDeclNGen_2284_);
                    leanh::lean_inc(v_ngen_2283_);
                    leanh::lean_inc(v_nextMacroScope_2282_);
                    leanh::lean_inc(v_env_2281_);
                    leanh::lean_dec(v___x_2279_);
                    v___x_2290_ = leanh::lean_box(0);
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_2292_ = leanh::lean_ctor_get_uint8(
                    v_infoState_2280_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_2293_ = leanh::lean_ctor_get(v_infoState_2280_, 0);
                v_lazyAssignment_2294_ = leanh::lean_ctor_get(v_infoState_2280_, 1);
                v_isSharedCheck_2310_ = (!leanh::lean_is_exclusive(v_infoState_2280_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v_unused_2311_ = leanh::lean_ctor_get(v_infoState_2280_, 2);
                    leanh::lean_dec(v_unused_2311_);
                    v___x_2296_ = v_infoState_2280_;
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_2294_);
                    leanh::lean_inc(v_assignment_2293_);
                    leanh::lean_dec(v_infoState_2280_);
                    v___x_2296_ = leanh::lean_box(0);
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2298_ = l_Lean_PersistentArray_append___redArg(v_a_2268_, v_a_2275_);
                leanh::lean_dec(v_a_2275_);
                if v_isShared_2297_ == 0 {
                    leanh::lean_ctor_set(v___x_2296_, 2, v___x_2298_);
                    v___x_2300_ = v___x_2296_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_assignment_2293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_lazyAssignment_2294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 2, v___x_2298_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2309_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_2292_,
                    );
                    v___x_2300_ = v_reuseFailAlloc_2309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2291_ == 0 {
                    leanh::lean_ctor_set(v___x_2290_, 7, v___x_2300_);
                    v___x_2302_ = v___x_2290_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_env_2281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_cache_2286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 6, v_messages_2287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 7, v___x_2300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2288_);
                    v___x_2302_ = v_reuseFailAlloc_2308_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2303_ = lean_st_ref_set(v___y_2259_, v___x_2302_);
                v___x_2304_ = leanh::lean_box(0);
                if v_isShared_2278_ == 0 {
                    leanh::lean_ctor_set(v___x_2277_, 0, v___x_2304_);
                    v___x_2306_ = v___x_2277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
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
                    v_reuseFailAlloc_2320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
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
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
    mut v___y_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v_a_2331_: *mut leanh::LeanObject,
    mut v_a_x3f_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2322_, v_ctx_x3f_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v_a_2331_, v_a_x3f_2332_);
    leanh::lean_dec(v_a_x3f_2332_);
    leanh::lean_dec_ref(v___y_2330_);
    leanh::lean_dec(v___y_2329_);
    leanh::lean_dec_ref(v___y_2328_);
    leanh::lean_dec(v___y_2327_);
    leanh::lean_dec_ref(v___y_2326_);
    leanh::lean_dec(v___y_2325_);
    leanh::lean_dec_ref(v___y_2324_);
    leanh::lean_dec(v___y_2322_);
    return v_res_2334_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2348_: u8 = 0;
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2371_: u8 = 0;
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_reuseFailAlloc_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_a_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_unused_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_st_ref_get(v___y_2344_);
                v_infoState_2347_ = leanh::lean_ctor_get(v___x_2346_, 7);
                leanh::lean_inc_ref(v_infoState_2347_);
                leanh::lean_dec(v___x_2346_);
                v_enabled_2348_ = leanh::lean_ctor_get_uint8(
                    v_infoState_2347_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_2347_);
                if v_enabled_2348_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_2336_);
                    leanh::lean_inc(v___y_2344_);
                    leanh::lean_inc_ref(v___y_2343_);
                    leanh::lean_inc(v___y_2342_);
                    leanh::lean_inc_ref(v___y_2341_);
                    leanh::lean_inc(v___y_2340_);
                    leanh::lean_inc_ref(v___y_2339_);
                    leanh::lean_inc(v___y_2338_);
                    leanh::lean_inc_ref(v___y_2337_);
                    v___x_2349_ = leanh::lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        leanh::lean_box(0),
                    );
                    return v___x_2349_;
                } else {
                    v___x_2350_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2344_);
                    v_a_2351_ = leanh::lean_ctor_get(v___x_2350_, 0);
                    leanh::lean_inc(v_a_2351_);
                    leanh::lean_dec_ref(v___x_2350_);
                    leanh::lean_inc(v___y_2344_);
                    leanh::lean_inc_ref(v___y_2343_);
                    leanh::lean_inc(v___y_2342_);
                    leanh::lean_inc_ref(v___y_2341_);
                    leanh::lean_inc(v___y_2340_);
                    leanh::lean_inc_ref(v___y_2339_);
                    leanh::lean_inc(v___y_2338_);
                    leanh::lean_inc_ref(v___y_2337_);
                    v_r_2352_ = leanh::lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_2352_) == 0 {
                        v_a_2353_ = leanh::lean_ctor_get(v_r_2352_, 0);
                        v_isSharedCheck_2377_ = (!leanh::lean_is_exclusive(v_r_2352_)) as u8;
                        if v_isSharedCheck_2377_ == 0 {
                            v___x_2355_ = v_r_2352_;
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2353_);
                            leanh::lean_dec(v_r_2352_);
                            v___x_2355_ = leanh::lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2378_ = leanh::lean_ctor_get(v_r_2352_, 0);
                        leanh::lean_inc(v_a_2378_);
                        leanh::lean_dec_ref_known(v_r_2352_, 1);
                        v___x_2379_ = leanh::lean_box(0);
                        v___x_2380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2379_);
                        if leanh::lean_obj_tag(v___x_2380_) == 0 {
                            v_isSharedCheck_2387_ =
                                (!leanh::lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2387_ == 0 {
                                v_unused_2388_ = leanh::lean_ctor_get(v___x_2380_, 0);
                                leanh::lean_dec(v_unused_2388_);
                                v___x_2382_ = v___x_2380_;
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2380_);
                                v___x_2382_ = leanh::lean_box(0);
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2378_);
                            v_a_2389_ = leanh::lean_ctor_get(v___x_2380_, 0);
                            v_isSharedCheck_2396_ =
                                (!leanh::lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2396_ == 0 {
                                v___x_2391_ = v___x_2380_;
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2389_);
                                leanh::lean_dec(v___x_2380_);
                                v___x_2391_ = leanh::lean_box(0);
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_2353_);
                if v_isShared_2356_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2355_, 1);
                    v___x_2358_ = v___x_2355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2358_);
                leanh::lean_dec_ref(v___x_2358_);
                if leanh::lean_obj_tag(v___x_2359_) == 0 {
                    v_isSharedCheck_2366_ = (!leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v_unused_2367_ = leanh::lean_ctor_get(v___x_2359_, 0);
                        leanh::lean_dec(v_unused_2367_);
                        v___x_2361_ = v___x_2359_;
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2359_);
                        v___x_2361_ = leanh::lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2353_);
                    v_a_2368_ = leanh::lean_ctor_get(v___x_2359_, 0);
                    v_isSharedCheck_2375_ = (!leanh::lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2375_ == 0 {
                        v___x_2370_ = v___x_2359_;
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2368_);
                        leanh::lean_dec(v___x_2359_);
                        v___x_2370_ = leanh::lean_box(0);
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2362_ == 0 {
                    leanh::lean_ctor_set(v___x_2361_, 0, v_a_2353_);
                    v___x_2364_ = v___x_2361_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2353_);
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
                    v_reuseFailAlloc_2374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
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
                    leanh::lean_ctor_set_tag(v___x_2382_, 1);
                    leanh::lean_ctor_set(v___x_2382_, 0, v_a_2378_);
                    v___x_2385_ = v___x_2382_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
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
                    v_reuseFailAlloc_2395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
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
    mut v_x_2397_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
    mut v___y_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2397_, v_ctx_x3f_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
    leanh::lean_dec(v___y_2406_);
    leanh::lean_dec_ref(v___y_2405_);
    leanh::lean_dec(v___y_2404_);
    leanh::lean_dec_ref(v___y_2403_);
    leanh::lean_dec(v___y_2402_);
    leanh::lean_dec_ref(v___y_2401_);
    leanh::lean_dec(v___y_2400_);
    leanh::lean_dec_ref(v___y_2399_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(
    mut v_x_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2420_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0;
    v___x_2421_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2410_, v___f_2420_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(
    mut v_x_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
    mut v___y_2425_: *mut leanh::LeanObject,
    mut v___y_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2430_);
    leanh::lean_dec_ref(v___y_2429_);
    leanh::lean_dec(v___y_2428_);
    leanh::lean_dec_ref(v___y_2427_);
    leanh::lean_dec(v___y_2426_);
    leanh::lean_dec_ref(v___y_2425_);
    leanh::lean_dec(v___y_2424_);
    leanh::lean_dec_ref(v___y_2423_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(
    mut v_00_u03b1_2433_: *mut leanh::LeanObject,
    mut v_x_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
    mut v___y_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2445_: *mut leanh::LeanObject,
    mut v_x_2446_: *mut leanh::LeanObject,
    mut v___y_2447_: *mut leanh::LeanObject,
    mut v___y_2448_: *mut leanh::LeanObject,
    mut v___y_2449_: *mut leanh::LeanObject,
    mut v___y_2450_: *mut leanh::LeanObject,
    mut v___y_2451_: *mut leanh::LeanObject,
    mut v___y_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2454_);
    leanh::lean_dec_ref(v___y_2453_);
    leanh::lean_dec(v___y_2452_);
    leanh::lean_dec_ref(v___y_2451_);
    leanh::lean_dec(v___y_2450_);
    leanh::lean_dec_ref(v___y_2449_);
    leanh::lean_dec(v___y_2448_);
    leanh::lean_dec_ref(v___y_2447_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalClassical(
    mut v_stx_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
    mut v_a_2460_: *mut leanh::LeanObject,
    mut v_a_2461_: *mut leanh::LeanObject,
    mut v_a_2462_: *mut leanh::LeanObject,
    mut v_a_2463_: *mut leanh::LeanObject,
    mut v_a_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
    mut v_a_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = leanh::lean_unsigned_to_nat(1);
    v___x_2469_ = l_Lean_Elab_Tactic_evalClassical___closed__0;
    v___x_2470_ = leanh::lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed as *mut core::ffi::c_void, 13, 4);
    leanh::lean_closure_set(v___x_2470_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2470_, 1, v___x_2468_);
    leanh::lean_closure_set(v___x_2470_, 2, v___x_2469_);
    leanh::lean_closure_set(v___x_2470_, 3, v_stx_2458_);
    v___x_2471_ = leanh::lean_alloc_closure(
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___x_2471_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2471_, 1, v___x_2470_);
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
    mut v_stx_2473_: *mut leanh::LeanObject,
    mut v_a_2474_: *mut leanh::LeanObject,
    mut v_a_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
    mut v_a_2478_: *mut leanh::LeanObject,
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
    mut v_a_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2481_);
    leanh::lean_dec_ref(v_a_2480_);
    leanh::lean_dec(v_a_2479_);
    leanh::lean_dec_ref(v_a_2478_);
    leanh::lean_dec(v_a_2477_);
    leanh::lean_dec_ref(v_a_2476_);
    leanh::lean_dec(v_a_2475_);
    leanh::lean_dec_ref(v_a_2474_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2484_: *mut leanh::LeanObject,
    mut v_stx_2485_: *mut leanh::LeanObject,
    mut v_act_2486_: *mut leanh::LeanObject,
    mut v___y_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
    mut v___y_2489_: *mut leanh::LeanObject,
    mut v___y_2490_: *mut leanh::LeanObject,
    mut v___y_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_2485_, v_act_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2497_: *mut leanh::LeanObject,
    mut v_stx_2498_: *mut leanh::LeanObject,
    mut v_act_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
    mut v___y_2506_: *mut leanh::LeanObject,
    mut v___y_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_2497_, v_stx_2498_, v_act_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
    leanh::lean_dec(v___y_2507_);
    leanh::lean_dec_ref(v___y_2506_);
    leanh::lean_dec(v___y_2505_);
    leanh::lean_dec_ref(v___y_2504_);
    leanh::lean_dec(v___y_2503_);
    leanh::lean_dec_ref(v___y_2502_);
    leanh::lean_dec(v___y_2501_);
    leanh::lean_dec_ref(v___y_2500_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(
    mut v_00_u03b1_2510_: *mut leanh::LeanObject,
    mut v_split_2511_: *mut leanh::LeanObject,
    mut v_act_2512_: *mut leanh::LeanObject,
    mut v_stx_2513_: *mut leanh::LeanObject,
    mut v___y_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
    mut v___y_2518_: *mut leanh::LeanObject,
    mut v___y_2519_: *mut leanh::LeanObject,
    mut v___y_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_2511_, v_act_2512_, v_stx_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
    return v___x_2523_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(
    mut v_00_u03b1_2524_: *mut leanh::LeanObject,
    mut v_split_2525_: *mut leanh::LeanObject,
    mut v_act_2526_: *mut leanh::LeanObject,
    mut v_stx_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_2524_, v_split_2525_, v_act_2526_, v_stx_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
    leanh::lean_dec(v___y_2535_);
    leanh::lean_dec_ref(v___y_2534_);
    leanh::lean_dec(v___y_2533_);
    leanh::lean_dec_ref(v___y_2532_);
    leanh::lean_dec(v___y_2531_);
    leanh::lean_dec_ref(v___y_2530_);
    leanh::lean_dec(v___y_2529_);
    leanh::lean_dec_ref(v___y_2528_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
    mut v___y_2540_: *mut leanh::LeanObject,
    mut v___y_2541_: *mut leanh::LeanObject,
    mut v___y_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_2543_, v___y_2544_, v___y_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(
    mut v___y_2548_: *mut leanh::LeanObject,
    mut v___y_2549_: *mut leanh::LeanObject,
    mut v___y_2550_: *mut leanh::LeanObject,
    mut v___y_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
    leanh::lean_dec(v___y_2555_);
    leanh::lean_dec_ref(v___y_2554_);
    leanh::lean_dec(v___y_2553_);
    leanh::lean_dec_ref(v___y_2552_);
    leanh::lean_dec(v___y_2551_);
    leanh::lean_dec_ref(v___y_2550_);
    leanh::lean_dec(v___y_2549_);
    leanh::lean_dec_ref(v___y_2548_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(
    mut v___y_2558_: *mut leanh::LeanObject,
    mut v___y_2559_: *mut leanh::LeanObject,
    mut v___y_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
    mut v___y_2563_: *mut leanh::LeanObject,
    mut v___y_2564_: *mut leanh::LeanObject,
    mut v___y_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2565_);
    return v___x_2567_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(
    mut v___y_2568_: *mut leanh::LeanObject,
    mut v___y_2569_: *mut leanh::LeanObject,
    mut v___y_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
    mut v___y_2572_: *mut leanh::LeanObject,
    mut v___y_2573_: *mut leanh::LeanObject,
    mut v___y_2574_: *mut leanh::LeanObject,
    mut v___y_2575_: *mut leanh::LeanObject,
    mut v___y_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    leanh::lean_dec(v___y_2575_);
    leanh::lean_dec_ref(v___y_2574_);
    leanh::lean_dec(v___y_2573_);
    leanh::lean_dec_ref(v___y_2572_);
    leanh::lean_dec(v___y_2571_);
    leanh::lean_dec_ref(v___y_2570_);
    leanh::lean_dec(v___y_2569_);
    leanh::lean_dec_ref(v___y_2568_);
    return v_res_2577_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(
    mut v_00_u03b1_2578_: *mut leanh::LeanObject,
    mut v_x_2579_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
    mut v___y_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
    mut v___y_2584_: *mut leanh::LeanObject,
    mut v___y_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
    mut v___y_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2579_, v_ctx_x3f_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
    return v___x_2590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(
    mut v_00_u03b1_2591_: *mut leanh::LeanObject,
    mut v_x_2592_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
    mut v___y_2598_: *mut leanh::LeanObject,
    mut v___y_2599_: *mut leanh::LeanObject,
    mut v___y_2600_: *mut leanh::LeanObject,
    mut v___y_2601_: *mut leanh::LeanObject,
    mut v___y_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2603_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_2591_, v_x_2592_, v_ctx_x3f_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
    leanh::lean_dec(v___y_2601_);
    leanh::lean_dec_ref(v___y_2600_);
    leanh::lean_dec(v___y_2599_);
    leanh::lean_dec_ref(v___y_2598_);
    leanh::lean_dec(v___y_2597_);
    leanh::lean_dec_ref(v___y_2596_);
    leanh::lean_dec(v___y_2595_);
    leanh::lean_dec_ref(v___y_2594_);
    return v_res_2603_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1()
-> *mut leanh::LeanObject {
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2622_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4;
    v___x_2623_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2624_ = leanh::lean_alloc_closure(
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
    mut v_a_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    return v_res_2627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3()
-> *mut leanh::LeanObject {
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2630_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_2629_);
    return v___x_2630_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(
    mut v_a_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2632_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    return v_res_2632_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Classical(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Classical(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Classical(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Classical(builtin);
}