// Lean compiler output
// Module: Lean.Elab.Tactic.Classical
// Imports: Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_9, lean_apply_10, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value: LeanStringObject<10> =
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
        m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0],
    };
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
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
            112, 114, 111, 112, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            10854111772627758120 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value)
                as *mut LeanObject,
            4643704380461739942 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_addInstance___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((10 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_classical___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_classical___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_classical___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_classical___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalClassical___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalTactic___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalClassical___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalClassical___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value) as *mut LeanObject,1538718060909595165 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value) as *mut LeanObject,3595078106460476937 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0(
    mut v_x_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1318_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1318_ = lean_ctor_get(v_x_1317_, 0);
    lean_inc(v_fst_1318_);
    return v_fst_1318_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed(
    mut v_x_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_Elab_Tactic_classical___redArg___lam__0(v_x_1319_);
    lean_dec_ref(v_x_1319_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1(
    mut v___x_1321_: *mut LeanObject,
    mut v_x_1322_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_1321_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed(
    mut v___x_1323_: *mut LeanObject,
    mut v_x_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1325_: *mut LeanObject = core::ptr::null_mut();
    v_res_1325_ = l_Lean_Elab_Tactic_classical___redArg___lam__1(v___x_1323_, v_x_1324_);
    lean_dec(v_x_1324_);
    lean_dec(v___x_1323_);
    return v_res_1325_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__2(
    mut v_toFunctor_1326_: *mut LeanObject,
    mut v___x_1327_: *mut LeanObject,
    mut v_modifyEnv_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
    mut v_t_1330_: *mut LeanObject,
    mut v___f_1331_: *mut LeanObject,
    mut v_____r_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v_map_1333_ = lean_ctor_get(v_toFunctor_1326_, 0);
    lean_inc(v_map_1333_);
    lean_dec_ref(v_toFunctor_1326_);
    v___x_1334_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_popScope as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1334_, 0, lean_box(0));
    lean_closure_set(v___x_1334_, 1, lean_box(0));
    lean_closure_set(v___x_1334_, 2, lean_box(0));
    lean_closure_set(v___x_1334_, 3, v___x_1327_);
    v___x_1335_ = lean_apply_1(v_modifyEnv_1328_, v___x_1334_);
    v___f_1336_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1336_, 0, v___x_1335_);
    v_y_1337_ = lean_apply_4(
        v_inst_1329_,
        lean_box(0),
        lean_box(0),
        v_t_1330_,
        v___f_1336_,
    );
    v___x_1338_ = lean_apply_4(
        v_map_1333_,
        lean_box(0),
        lean_box(0),
        v___f_1331_,
        v_y_1337_,
    );
    return v___x_1338_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg___lam__3(
    mut v_inst_1349_: *mut LeanObject,
    mut v_toBind_1350_: *mut LeanObject,
    mut v___f_1351_: *mut LeanObject,
    mut v_____r_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3;
    v___x_1354_ = lean_apply_2(v_inst_1349_, lean_box(0), v___x_1353_);
    v___x_1355_ = lean_apply_4(
        v_toBind_1350_,
        lean_box(0),
        lean_box(0),
        v___x_1354_,
        v___f_1351_,
    );
    return v___x_1355_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lean_Meta_instanceExtension;
    v___x_1358_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_pushScope as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1358_, 0, lean_box(0));
    lean_closure_set(v___x_1358_, 1, lean_box(0));
    lean_closure_set(v___x_1358_, 2, lean_box(0));
    lean_closure_set(v___x_1358_, 3, v___x_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___redArg(
    mut v_inst_1359_: *mut LeanObject,
    mut v_inst_1360_: *mut LeanObject,
    mut v_inst_1361_: *mut LeanObject,
    mut v_inst_1362_: *mut LeanObject,
    mut v_t_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1364_ = lean_ctor_get(v_inst_1359_, 0);
    lean_inc_ref(v_toApplicative_1364_);
    v_toBind_1365_ = lean_ctor_get(v_inst_1359_, 1);
    lean_inc_n(v_toBind_1365_, 2);
    lean_dec_ref(v_inst_1359_);
    v_modifyEnv_1366_ = lean_ctor_get(v_inst_1360_, 1);
    lean_inc_n(v_modifyEnv_1366_, 2);
    lean_dec_ref(v_inst_1360_);
    v_toFunctor_1367_ = lean_ctor_get(v_toApplicative_1364_, 0);
    lean_inc_ref(v_toFunctor_1367_);
    lean_dec_ref(v_toApplicative_1364_);
    v___f_1368_ = l_Lean_Elab_Tactic_classical___redArg___closed__0;
    v___x_1369_ = l_Lean_Meta_instanceExtension;
    v___x_1370_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_classical___redArg___closed__1,
    );
    v___x_1371_ = lean_apply_1(v_modifyEnv_1366_, v___x_1370_);
    v___f_1372_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1372_, 0, v_toFunctor_1367_);
    lean_closure_set(v___f_1372_, 1, v___x_1369_);
    lean_closure_set(v___f_1372_, 2, v_modifyEnv_1366_);
    lean_closure_set(v___f_1372_, 3, v_inst_1361_);
    lean_closure_set(v___f_1372_, 4, v_t_1363_);
    lean_closure_set(v___f_1372_, 5, v___f_1368_);
    v___f_1373_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_classical___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1373_, 0, v_inst_1362_);
    lean_closure_set(v___f_1373_, 1, v_toBind_1365_);
    lean_closure_set(v___f_1373_, 2, v___f_1372_);
    v___x_1374_ = lean_apply_4(
        v_toBind_1365_,
        lean_box(0),
        lean_box(0),
        v___x_1371_,
        v___f_1373_,
    );
    return v___x_1374_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical(
    mut v_m_1375_: *mut LeanObject,
    mut v_00_u03b1_1376_: *mut LeanObject,
    mut v_inst_1377_: *mut LeanObject,
    mut v_inst_1378_: *mut LeanObject,
    mut v_inst_1379_: *mut LeanObject,
    mut v_inst_1380_: *mut LeanObject,
    mut v_t_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___y_1383_: *mut LeanObject,
    mut v___x_1384_: *mut LeanObject,
    mut v___x_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___x_1387_: *mut LeanObject,
    mut v_a_x3f_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1423_: u8 = 0;
    let mut v_unused_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_st_ref_take(v___y_1383_);
                v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
                v_nextMacroScope_1392_ = lean_ctor_get(v___x_1390_, 1);
                v_ngen_1393_ = lean_ctor_get(v___x_1390_, 2);
                v_auxDeclNGen_1394_ = lean_ctor_get(v___x_1390_, 3);
                v_traceState_1395_ = lean_ctor_get(v___x_1390_, 4);
                v_messages_1396_ = lean_ctor_get(v___x_1390_, 6);
                v_infoState_1397_ = lean_ctor_get(v___x_1390_, 7);
                v_snapshotTasks_1398_ = lean_ctor_get(v___x_1390_, 8);
                v_isSharedCheck_1423_ = (!lean_is_exclusive(v___x_1390_)) as u8;
                if v_isSharedCheck_1423_ == 0 {
                    v_unused_1424_ = lean_ctor_get(v___x_1390_, 5);
                    lean_dec(v_unused_1424_);
                    v___x_1400_ = v___x_1390_;
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1398_);
                    lean_inc(v_infoState_1397_);
                    lean_inc(v_messages_1396_);
                    lean_inc(v_traceState_1395_);
                    lean_inc(v_auxDeclNGen_1394_);
                    lean_inc(v_ngen_1393_);
                    lean_inc(v_nextMacroScope_1392_);
                    lean_inc(v_env_1391_);
                    lean_dec(v___x_1390_);
                    v___x_1400_ = lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1402_ = l_Lean_ScopedEnvExtension_popScope___redArg(v___x_1384_, v_env_1391_);
                if v_isShared_1401_ == 0 {
                    lean_ctor_set(v___x_1400_, 5, v___x_1385_);
                    lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1402_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_nextMacroScope_1392_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_ngen_1393_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_auxDeclNGen_1394_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_traceState_1395_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 5, v___x_1385_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_messages_1396_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_infoState_1397_);
                    lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_snapshotTasks_1398_);
                    v___x_1404_ = v_reuseFailAlloc_1422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1405_ = lean_st_ref_set(v___y_1383_, v___x_1404_);
                v___x_1406_ = lean_st_ref_take(v___y_1386_);
                v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
                v_zetaDeltaFVarIds_1408_ = lean_ctor_get(v___x_1406_, 2);
                v_postponed_1409_ = lean_ctor_get(v___x_1406_, 3);
                v_diag_1410_ = lean_ctor_get(v___x_1406_, 4);
                v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1406_)) as u8;
                if v_isSharedCheck_1420_ == 0 {
                    v_unused_1421_ = lean_ctor_get(v___x_1406_, 1);
                    lean_dec(v_unused_1421_);
                    v___x_1412_ = v___x_1406_;
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1410_);
                    lean_inc(v_postponed_1409_);
                    lean_inc(v_zetaDeltaFVarIds_1408_);
                    lean_inc(v_mctx_1407_);
                    lean_dec(v___x_1406_);
                    v___x_1412_ = lean_box(0);
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1413_ == 0 {
                    lean_ctor_set(v___x_1412_, 1, v___x_1387_);
                    v___x_1415_ = v___x_1412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_mctx_1407_);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1387_);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_zetaDeltaFVarIds_1408_);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_postponed_1409_);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_diag_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1416_ = lean_st_ref_set(v___y_1386_, v___x_1415_);
                v___x_1417_ = lean_box(0);
                v___x_1418_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1418_, 0, v___x_1417_);
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(
    mut v___y_1425_: *mut LeanObject,
    mut v___x_1426_: *mut LeanObject,
    mut v___x_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___x_1429_: *mut LeanObject,
    mut v_a_x3f_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1432_: *mut LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1425_, v___x_1426_, v___x_1427_, v___y_1428_, v___x_1429_, v_a_x3f_1430_);
    lean_dec(v_a_x3f_1430_);
    lean_dec(v___y_1428_);
    lean_dec(v___y_1425_);
    return v_res_1432_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1433_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
    v___x_1435_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1436_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1437_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1437_, 0, v___x_1436_);
    lean_ctor_set(v___x_1437_, 1, v___x_1436_);
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
    v___x_1439_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    lean_ctor_set(v___x_1439_, 1, v___x_1438_);
    lean_ctor_set(v___x_1439_, 2, v___x_1438_);
    lean_ctor_set(v___x_1439_, 3, v___x_1438_);
    lean_ctor_set(v___x_1439_, 4, v___x_1438_);
    lean_ctor_set(v___x_1439_, 5, v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(
    mut v_t_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_unused_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_a_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_unused_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_reuseFailAlloc_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1522_: u8 = 0;
    let mut v_unused_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1450_ = lean_st_ref_take(v___y_1448_);
                v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
                v_nextMacroScope_1452_ = lean_ctor_get(v___x_1450_, 1);
                v_ngen_1453_ = lean_ctor_get(v___x_1450_, 2);
                v_auxDeclNGen_1454_ = lean_ctor_get(v___x_1450_, 3);
                v_traceState_1455_ = lean_ctor_get(v___x_1450_, 4);
                v_messages_1456_ = lean_ctor_get(v___x_1450_, 6);
                v_infoState_1457_ = lean_ctor_get(v___x_1450_, 7);
                v_snapshotTasks_1458_ = lean_ctor_get(v___x_1450_, 8);
                v_isSharedCheck_1525_ = (!lean_is_exclusive(v___x_1450_)) as u8;
                if v_isSharedCheck_1525_ == 0 {
                    v_unused_1526_ = lean_ctor_get(v___x_1450_, 5);
                    lean_dec(v_unused_1526_);
                    v___x_1460_ = v___x_1450_;
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1458_);
                    lean_inc(v_infoState_1457_);
                    lean_inc(v_messages_1456_);
                    lean_inc(v_traceState_1455_);
                    lean_inc(v_auxDeclNGen_1454_);
                    lean_inc(v_ngen_1453_);
                    lean_inc(v_nextMacroScope_1452_);
                    lean_inc(v_env_1451_);
                    lean_dec(v___x_1450_);
                    v___x_1460_ = lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1462_ = l_Lean_Meta_instanceExtension;
                v___x_1463_ =
                    l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_1462_, v_env_1451_);
                v___x_1464_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
                if v_isShared_1461_ == 0 {
                    lean_ctor_set(v___x_1460_, 5, v___x_1464_);
                    lean_ctor_set(v___x_1460_, 0, v___x_1463_);
                    v___x_1466_ = v___x_1460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1463_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1452_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1453_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_traceState_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 5, v___x_1464_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_messages_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_infoState_1457_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_snapshotTasks_1458_);
                    v___x_1466_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1467_ = lean_st_ref_set(v___y_1448_, v___x_1466_);
                v___x_1468_ = lean_st_ref_take(v___y_1446_);
                v_mctx_1469_ = lean_ctor_get(v___x_1468_, 0);
                v_zetaDeltaFVarIds_1470_ = lean_ctor_get(v___x_1468_, 2);
                v_postponed_1471_ = lean_ctor_get(v___x_1468_, 3);
                v_diag_1472_ = lean_ctor_get(v___x_1468_, 4);
                v_isSharedCheck_1522_ = (!lean_is_exclusive(v___x_1468_)) as u8;
                if v_isSharedCheck_1522_ == 0 {
                    v_unused_1523_ = lean_ctor_get(v___x_1468_, 1);
                    lean_dec(v_unused_1523_);
                    v___x_1474_ = v___x_1468_;
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1472_);
                    lean_inc(v_postponed_1471_);
                    lean_inc(v_zetaDeltaFVarIds_1470_);
                    lean_inc(v_mctx_1469_);
                    lean_dec(v___x_1468_);
                    v___x_1474_ = lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1522_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1476_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once), _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
                if v_isShared_1475_ == 0 {
                    lean_ctor_set(v___x_1474_, 1, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_mctx_1469_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1476_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_zetaDeltaFVarIds_1470_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_postponed_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_diag_1472_);
                    v___x_1478_ = v_reuseFailAlloc_1521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1479_ = lean_st_ref_set(v___y_1446_, v___x_1478_);
                v___x_1480_ = l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2;
                v___x_1481_ = 1;
                v___x_1482_ = lean_unsigned_to_nat(10);
                v___x_1483_ = l_Lean_Meta_addInstance(
                    v___x_1480_,
                    v___x_1481_,
                    v___x_1482_,
                    v___y_1445_,
                    v___y_1446_,
                    v___y_1447_,
                    v___y_1448_,
                );
                if lean_obj_tag(v___x_1483_) == 0 {
                    lean_dec_ref_known(v___x_1483_, 1);
                    lean_inc(v___y_1448_);
                    lean_inc_ref(v___y_1447_);
                    lean_inc(v___y_1446_);
                    lean_inc_ref(v___y_1445_);
                    lean_inc(v___y_1444_);
                    lean_inc_ref(v___y_1443_);
                    lean_inc(v___y_1442_);
                    lean_inc_ref(v___y_1441_);
                    v_r_1484_ = lean_apply_9(
                        v_t_1440_,
                        v___y_1441_,
                        v___y_1442_,
                        v___y_1443_,
                        v___y_1444_,
                        v___y_1445_,
                        v___y_1446_,
                        v___y_1447_,
                        v___y_1448_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_1484_) == 0 {
                        v_a_1485_ = lean_ctor_get(v_r_1484_, 0);
                        v_isSharedCheck_1501_ = (!lean_is_exclusive(v_r_1484_)) as u8;
                        if v_isSharedCheck_1501_ == 0 {
                            v___x_1487_ = v_r_1484_;
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1485_);
                            lean_dec(v_r_1484_);
                            v___x_1487_ = lean_box(0);
                            v_isShared_1488_ = v_isSharedCheck_1501_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1502_ = lean_ctor_get(v_r_1484_, 0);
                        lean_inc(v_a_1502_);
                        lean_dec_ref_known(v_r_1484_, 1);
                        v___x_1503_ = lean_box(0);
                        v___x_1504_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1503_);
                        v_isSharedCheck_1511_ = (!lean_is_exclusive(v___x_1504_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v_unused_1512_ = lean_ctor_get(v___x_1504_, 0);
                            lean_dec(v_unused_1512_);
                            v___x_1506_ = v___x_1504_;
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v___x_1504_);
                            v___x_1506_ = lean_box(0);
                            v_isShared_1507_ = v_isSharedCheck_1511_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_t_1440_);
                    v_a_1513_ = lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1520_ = (!lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1520_ == 0 {
                        v___x_1515_ = v___x_1483_;
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1513_);
                        lean_dec(v___x_1483_);
                        v___x_1515_ = lean_box(0);
                        v_isShared_1516_ = v_isSharedCheck_1520_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_1485_);
                if v_isShared_1488_ == 0 {
                    lean_ctor_set_tag(v___x_1487_, 1);
                    v___x_1490_ = v___x_1487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1485_);
                    v___x_1490_ = v_reuseFailAlloc_1500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1491_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_1448_, v___x_1462_, v___x_1464_, v___y_1446_, v___x_1476_, v___x_1490_);
                lean_dec_ref(v___x_1490_);
                v_isSharedCheck_1498_ = (!lean_is_exclusive(v___x_1491_)) as u8;
                if v_isSharedCheck_1498_ == 0 {
                    v_unused_1499_ = lean_ctor_get(v___x_1491_, 0);
                    lean_dec(v_unused_1499_);
                    v___x_1493_ = v___x_1491_;
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_1491_);
                    v___x_1493_ = lean_box(0);
                    v_isShared_1494_ = v_isSharedCheck_1498_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1494_ == 0 {
                    lean_ctor_set(v___x_1493_, 0, v_a_1485_);
                    v___x_1496_ = v___x_1493_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1485_);
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
                    lean_ctor_set_tag(v___x_1506_, 1);
                    lean_ctor_set(v___x_1506_, 0, v_a_1502_);
                    v___x_1509_ = v___x_1506_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1502_);
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
                    v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
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
    mut v_t_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
    mut v___y_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1537_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1535_);
    lean_dec_ref(v___y_1534_);
    lean_dec(v___y_1533_);
    lean_dec_ref(v___y_1532_);
    lean_dec(v___y_1531_);
    lean_dec_ref(v___y_1530_);
    lean_dec(v___y_1529_);
    lean_dec_ref(v___y_1528_);
    return v_res_1537_;
}
pub unsafe fn l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(
    mut v_00_u03b1_1538_: *mut LeanObject,
    mut v_t_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
    mut v___y_1542_: *mut LeanObject,
    mut v___y_1543_: *mut LeanObject,
    mut v___y_1544_: *mut LeanObject,
    mut v___y_1545_: *mut LeanObject,
    mut v___y_1546_: *mut LeanObject,
    mut v___y_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1550_: *mut LeanObject,
    mut v_t_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
    mut v___y_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1561_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1559_);
    lean_dec_ref(v___y_1558_);
    lean_dec(v___y_1557_);
    lean_dec_ref(v___y_1556_);
    lean_dec(v___y_1555_);
    lean_dec_ref(v___y_1554_);
    lean_dec(v___y_1553_);
    lean_dec_ref(v___y_1552_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(
    mut v_stx_1562_: *mut LeanObject,
    mut v_act_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
    mut v___y_1568_: *mut LeanObject,
    mut v___y_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1584_: u8 = 0;
    let mut v_cancelTk_x3f_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1586_: u8 = 0;
    let mut v_inheritedTraceOptions_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1573_ = lean_ctor_get(v___y_1570_, 0);
                v_fileMap_1574_ = lean_ctor_get(v___y_1570_, 1);
                v_options_1575_ = lean_ctor_get(v___y_1570_, 2);
                v_currRecDepth_1576_ = lean_ctor_get(v___y_1570_, 3);
                v_maxRecDepth_1577_ = lean_ctor_get(v___y_1570_, 4);
                v_currNamespace_1578_ = lean_ctor_get(v___y_1570_, 6);
                v_openDecls_1579_ = lean_ctor_get(v___y_1570_, 7);
                v_initHeartbeats_1580_ = lean_ctor_get(v___y_1570_, 8);
                v_maxHeartbeats_1581_ = lean_ctor_get(v___y_1570_, 9);
                v_quotContext_1582_ = lean_ctor_get(v___y_1570_, 10);
                v_currMacroScope_1583_ = lean_ctor_get(v___y_1570_, 11);
                v_diag_1584_ = lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1585_ = lean_ctor_get(v___y_1570_, 12);
                v_suppressElabErrors_1586_ = lean_ctor_get_uint8(
                    v___y_1570_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1587_ = lean_ctor_get(v___y_1570_, 13);
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
                lean_inc_ref(v_inheritedTraceOptions_1587_);
                lean_inc(v_cancelTk_x3f_1585_);
                lean_inc(v_currMacroScope_1583_);
                lean_inc(v_quotContext_1582_);
                lean_inc(v_maxHeartbeats_1581_);
                lean_inc(v_initHeartbeats_1580_);
                lean_inc(v_openDecls_1579_);
                lean_inc(v_currNamespace_1578_);
                lean_inc(v_maxRecDepth_1577_);
                lean_inc(v_currRecDepth_1576_);
                lean_inc_ref(v_options_1575_);
                lean_inc_ref(v_fileMap_1574_);
                lean_inc_ref(v_fileName_1573_);
                v___x_1590_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1590_, 0, v_fileName_1573_);
                lean_ctor_set(v___x_1590_, 1, v_fileMap_1574_);
                lean_ctor_set(v___x_1590_, 2, v_options_1575_);
                lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1576_);
                lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1577_);
                lean_ctor_set(v___x_1590_, 5, v_stx_1562_);
                lean_ctor_set(v___x_1590_, 6, v_currNamespace_1578_);
                lean_ctor_set(v___x_1590_, 7, v_openDecls_1579_);
                lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1580_);
                lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1581_);
                lean_ctor_set(v___x_1590_, 10, v_quotContext_1582_);
                lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1583_);
                lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1585_);
                lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1587_);
                lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_1584_,
                );
                lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___y_1589_,
                );
                lean_inc(v___y_1571_);
                lean_inc(v___y_1569_);
                lean_inc_ref(v___y_1568_);
                lean_inc(v___y_1567_);
                lean_inc_ref(v___y_1566_);
                lean_inc(v___y_1565_);
                lean_inc_ref(v___y_1564_);
                v___x_1591_ = lean_apply_9(
                    v_act_1563_,
                    v___y_1564_,
                    v___y_1565_,
                    v___y_1566_,
                    v___y_1567_,
                    v___y_1568_,
                    v___y_1569_,
                    v___x_1590_,
                    v___y_1571_,
                    lean_box(0),
                );
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_stx_1593_: *mut LeanObject,
    mut v_act_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1604_: *mut LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1593_, v_act_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
    lean_dec(v___y_1602_);
    lean_dec_ref(v___y_1601_);
    lean_dec(v___y_1600_);
    lean_dec_ref(v___y_1599_);
    lean_dec(v___y_1598_);
    lean_dec_ref(v___y_1597_);
    lean_dec(v___y_1596_);
    lean_dec_ref(v___y_1595_);
    return v_res_1604_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(
    mut v_act_1605_: *mut LeanObject,
    mut v_snd_1606_: *mut LeanObject,
    mut v_____r_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_snd_1606_);
    v___x_1617_ = lean_apply_1(v_act_1605_, v_snd_1606_);
    v___x_1618_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_1606_, v___x_1617_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_act_1619_: *mut LeanObject,
    mut v_snd_1620_: *mut LeanObject,
    mut v_____r_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1631_: *mut LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_1619_, v_snd_1620_, v_____r_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
    lean_dec(v___y_1629_);
    lean_dec_ref(v___y_1628_);
    lean_dec(v___y_1627_);
    lean_dec_ref(v___y_1626_);
    lean_dec(v___y_1625_);
    lean_dec_ref(v___y_1624_);
    lean_dec(v___y_1623_);
    lean_dec_ref(v___y_1622_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(
    mut v_val_1633_: *mut LeanObject,
    mut v___f_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tacSnap_x3f_1649_ = lean_ctor_get(v___y_1637_, 6);
                if lean_obj_tag(v_tacSnap_x3f_1649_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_1650_ = lean_ctor_get(v_tacSnap_x3f_1649_, 0);
                    v_old_x3f_1651_ = lean_ctor_get(v_val_1650_, 0);
                    if lean_obj_tag(v_old_x3f_1651_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_val_1633_);
                        v___x_1652_ = lean_box(0);
                        v___x_1653_ = lean_apply_10(
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
                            lean_box(0),
                        );
                        return v___x_1653_;
                    }
                }
            }
            1 => {
                v_val_1645_ = lean_ctor_get(v_val_1633_, 1);
                lean_inc(v_val_1645_);
                lean_dec_ref(v_val_1633_);
                v___x_1646_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0;
                v___x_1647_ =
                    l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_1646_, v_val_1645_);
                v___x_1648_ = lean_apply_10(
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
                    lean_box(0),
                );
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(
    mut v_val_1654_: *mut LeanObject,
    mut v___f_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1665_: *mut LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_1654_, v___f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(
    mut v_split_1666_: *mut LeanObject,
    mut v_act_1667_: *mut LeanObject,
    mut v_stx_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1679_: u8 = 0;
    let mut v___y_1680_: u8 = 0;
    let mut v___y_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: u8 = 0;
    let mut v___y_1684_: u8 = 0;
    let mut v___y_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: u8 = 0;
    let mut v___y_1688_: u8 = 0;
    let mut v___y_1689_: u8 = 0;
    let mut v___y_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: u8 = 0;
    let mut v___y_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: u8 = 0;
    let mut v___y_1694_: u8 = 0;
    let mut v___y_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: u8 = 0;
    let mut v___y_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: u8 = 0;
    let mut v___y_1703_: u8 = 0;
    let mut v___y_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: u8 = 0;
    let mut v___y_1707_: u8 = 0;
    let mut v___y_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_new_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: u8 = 0;
    let mut v___y_1712_: u8 = 0;
    let mut v___y_1713_: u8 = 0;
    let mut v___y_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: u8 = 0;
    let mut v___y_1716_: u8 = 0;
    let mut v___y_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: u8 = 0;
    let mut v___y_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: u8 = 0;
    let mut v___y_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_1731_: u8 = 0;
    let mut v_errToSorry_1732_: u8 = 0;
    let mut v_autoBoundImplicitContext_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sectionVars_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_1737_: u8 = 0;
    let mut v_heedElabAsElim_1738_: u8 = 0;
    let mut v_isNoncomputableSection_1739_: u8 = 0;
    let mut v_isMetaSection_1740_: u8 = 0;
    let mut v_ignoreTCFailures_1741_: u8 = 0;
    let mut v_inPattern_1742_: u8 = 0;
    let mut v_tacSnap_x3f_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_1744_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_1745_: u8 = 0;
    let mut v_checkDeprecated_1746_: u8 = 0;
    let mut v_fixedTermElabs_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_new_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_new_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v___f_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_split_1666_);
                v___x_1725_ = lean_apply_1(v_split_1666_, v_stx_1668_);
                v_fst_1726_ = lean_ctor_get(v___x_1725_, 0);
                lean_inc(v_fst_1726_);
                v_snd_1727_ = lean_ctor_get(v___x_1725_, 1);
                lean_inc_n(v_snd_1727_, 2);
                lean_dec_ref(v___x_1725_);
                v_options_1728_ = lean_ctor_get(v___y_1675_, 2);
                v_declName_x3f_1729_ = lean_ctor_get(v___y_1671_, 0);
                v_macroStack_1730_ = lean_ctor_get(v___y_1671_, 1);
                v_mayPostpone_1731_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                v_errToSorry_1732_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_1733_ = lean_ctor_get(v___y_1671_, 2);
                v_autoBoundImplicitForbidden_1734_ = lean_ctor_get(v___y_1671_, 3);
                v_sectionVars_1735_ = lean_ctor_get(v___y_1671_, 4);
                v_sectionFVars_1736_ = lean_ctor_get(v___y_1671_, 5);
                v_implicitLambda_1737_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_1738_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_1739_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_1740_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_1741_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_1742_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_1743_ = lean_ctor_get(v___y_1671_, 6);
                v_saveRecAppSyntax_1744_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_1745_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_1746_ = lean_ctor_get_uint8(
                    v___y_1671_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_1747_ = lean_ctor_get(v___y_1671_, 7);
                lean_inc_ref(v_act_1667_);
                v___f_1770_ = lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 2);
                lean_closure_set(v___f_1770_, 0, v_act_1667_);
                lean_closure_set(v___f_1770_, 1, v_snd_1727_);
                if lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    lean_dec_ref(v___f_1770_);
                    state = 6;
                    continue;
                } else {
                    v_val_1774_ = lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1775_ = lean_ctor_get(v_val_1774_, 0);
                    if lean_obj_tag(v_old_x3f_1775_) == 1 {
                        lean_dec(v_snd_1727_);
                        lean_dec_ref(v_act_1667_);
                        v_val_1776_ = lean_ctor_get(v_old_x3f_1775_, 0);
                        lean_inc(v_val_1776_);
                        v___f_1777_ = lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 11, 2);
                        lean_closure_set(v___f_1777_, 0, v_val_1776_);
                        lean_closure_set(v___f_1777_, 1, v___f_1770_);
                        v___y_1749_ = v___f_1777_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v___f_1770_);
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_1695_);
                lean_inc(v___y_1690_);
                lean_inc(v___y_1682_);
                lean_inc_ref(v___y_1686_);
                lean_inc(v___y_1681_);
                lean_inc(v___y_1685_);
                lean_inc(v___y_1696_);
                v___x_1699_ = lean_alloc_ctor(0, 8, (11) as u32);
                lean_ctor_set(v___x_1699_, 0, v___y_1696_);
                lean_ctor_set(v___x_1699_, 1, v___y_1685_);
                lean_ctor_set(v___x_1699_, 2, v___y_1681_);
                lean_ctor_set(v___x_1699_, 3, v___y_1686_);
                lean_ctor_set(v___x_1699_, 4, v___y_1682_);
                lean_ctor_set(v___x_1699_, 5, v___y_1690_);
                lean_ctor_set(v___x_1699_, 6, v___y_1698_);
                lean_ctor_set(v___x_1699_, 7, v___y_1695_);
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    v___y_1680_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                    v___y_1687_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                    v___y_1697_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                    v___y_1684_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 4) as u32,
                    v___y_1688_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 5) as u32,
                    v___y_1694_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 6) as u32,
                    v___y_1691_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 7) as u32,
                    v___y_1679_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 8) as u32,
                    v___y_1693_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 9) as u32,
                    v___y_1683_,
                );
                lean_ctor_set_uint8(
                    v___x_1699_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 10) as u32,
                    v___y_1689_,
                );
                lean_inc(v___y_1676_);
                lean_inc_ref(v___y_1675_);
                lean_inc(v___y_1674_);
                lean_inc_ref(v___y_1673_);
                lean_inc(v___y_1672_);
                lean_inc(v___y_1670_);
                lean_inc_ref(v___y_1669_);
                v___x_1700_ = lean_apply_9(
                    v___y_1692_,
                    v___y_1669_,
                    v___y_1670_,
                    v___x_1699_,
                    v___y_1672_,
                    v___y_1673_,
                    v___y_1674_,
                    v___y_1675_,
                    v___y_1676_,
                    lean_box(0),
                );
                return v___x_1700_;
            }
            2 => {
                v___x_1723_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1723_, 0, v___y_1722_);
                lean_ctor_set(v___x_1723_, 1, v_new_1709_);
                v___x_1724_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1724_, 0, v___x_1723_);
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
                if lean_obj_tag(v_tacSnap_x3f_1743_) == 0 {
                    lean_dec(v_fst_1726_);
                    lean_dec_ref(v_split_1666_);
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
                    v_val_1750_ = lean_ctor_get(v_tacSnap_x3f_1743_, 0);
                    v_old_x3f_1751_ = lean_ctor_get(v_val_1750_, 0);
                    if lean_obj_tag(v_old_x3f_1751_) == 0 {
                        lean_dec(v_fst_1726_);
                        lean_dec_ref(v_split_1666_);
                        v_new_1752_ = lean_ctor_get(v_val_1750_, 1);
                        lean_inc(v_new_1752_);
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
                        v_val_1753_ = lean_ctor_get(v_old_x3f_1751_, 0);
                        v_new_1754_ = lean_ctor_get(v_val_1750_, 1);
                        v_stx_1755_ = lean_ctor_get(v_val_1753_, 0);
                        v_val_1756_ = lean_ctor_get(v_val_1753_, 1);
                        lean_inc(v_stx_1755_);
                        v___x_1757_ = lean_apply_1(v_split_1666_, v_stx_1755_);
                        v_fst_1758_ = lean_ctor_get(v___x_1757_, 0);
                        v_snd_1759_ = lean_ctor_get(v___x_1757_, 1);
                        v_isSharedCheck_1769_ = (!lean_is_exclusive(v___x_1757_)) as u8;
                        if v_isSharedCheck_1769_ == 0 {
                            v___x_1761_ = v___x_1757_;
                            v_isShared_1762_ = v_isSharedCheck_1769_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_1759_);
                            lean_inc(v_fst_1758_);
                            lean_dec(v___x_1757_);
                            v___x_1761_ = lean_box(0);
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
                    lean_del_object(v___x_1761_);
                    lean_dec(v_snd_1759_);
                    v___x_1764_ = lean_box(0);
                    lean_inc(v_new_1754_);
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
                    lean_inc(v_val_1756_);
                    if v_isShared_1762_ == 0 {
                        lean_ctor_set(v___x_1761_, 1, v_val_1756_);
                        lean_ctor_set(v___x_1761_, 0, v_snd_1759_);
                        v___x_1766_ = v___x_1761_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_snd_1759_);
                        lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_val_1756_);
                        v___x_1766_ = v_reuseFailAlloc_1768_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1767_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1767_, 0, v___x_1766_);
                lean_inc(v_new_1754_);
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
                v___x_1772_ = lean_box(0);
                v___x_1773_ = lean_alloc_closure(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 3);
                lean_closure_set(v___x_1773_, 0, v_act_1667_);
                lean_closure_set(v___x_1773_, 1, v_snd_1727_);
                lean_closure_set(v___x_1773_, 2, v___x_1772_);
                v___y_1749_ = v___x_1773_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(
    mut v_split_1778_: *mut LeanObject,
    mut v_act_1779_: *mut LeanObject,
    mut v_stx_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1790_: *mut LeanObject = core::ptr::null_mut();
    v_res_1790_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1778_, v_act_1779_, v_stx_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
    lean_dec(v___y_1788_);
    lean_dec_ref(v___y_1787_);
    lean_dec(v___y_1786_);
    lean_dec_ref(v___y_1785_);
    lean_dec(v___y_1784_);
    lean_dec_ref(v___y_1783_);
    lean_dec(v___y_1782_);
    lean_dec_ref(v___y_1781_);
    return v_res_1790_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(
    mut v_argIdx_1794_: *mut LeanObject,
    mut v_stx_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Syntax_getArgs(v_stx_1795_);
    v___x_1797_ = lean_unsigned_to_nat(0);
    lean_inc(v_argIdx_1794_);
    v___x_1798_ = l_Array_toSubarray___redArg(v___x_1796_, v___x_1797_, v_argIdx_1794_);
    v___x_1799_ = l_Subarray_copy___redArg(v___x_1798_);
    v___x_1800_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1;
    v___x_1801_ = lean_box(2);
    v___x_1802_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    lean_ctor_set(v___x_1802_, 1, v___x_1800_);
    lean_ctor_set(v___x_1802_, 2, v___x_1799_);
    v___x_1803_ = l_Lean_Syntax_getArg(v_stx_1795_, v_argIdx_1794_);
    lean_dec(v_argIdx_1794_);
    v___x_1804_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1804_, 0, v___x_1802_);
    lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(
    mut v_argIdx_1805_: *mut LeanObject,
    mut v_stx_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1807_: *mut LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_1805_, v_stx_1806_);
    lean_dec(v_stx_1806_);
    return v_res_1807_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(
    mut v_argIdx_1808_: *mut LeanObject,
    mut v_act_1809_: *mut LeanObject,
    mut v_stx_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___f_1820_ = lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1820_, 0, v_argIdx_1808_);
    v___x_1821_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_1820_, v_act_1809_, v_stx_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(
    mut v_argIdx_1822_: *mut LeanObject,
    mut v_act_1823_: *mut LeanObject,
    mut v_stx_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1822_, v_act_1823_, v_stx_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    lean_dec(v___y_1832_);
    lean_dec_ref(v___y_1831_);
    lean_dec(v___y_1830_);
    lean_dec_ref(v___y_1829_);
    lean_dec(v___y_1828_);
    lean_dec_ref(v___y_1827_);
    lean_dec(v___y_1826_);
    lean_dec_ref(v___y_1825_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(
    mut v_00_u03b1_1835_: *mut LeanObject,
    mut v_argIdx_1836_: *mut LeanObject,
    mut v_act_1837_: *mut LeanObject,
    mut v_stx_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_1836_, v_act_1837_, v_stx_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    return v___x_1848_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_argIdx_1850_: *mut LeanObject,
    mut v_act_1851_: *mut LeanObject,
    mut v_stx_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1862_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1860_);
    lean_dec_ref(v___y_1859_);
    lean_dec(v___y_1858_);
    lean_dec_ref(v___y_1857_);
    lean_dec(v___y_1856_);
    lean_dec_ref(v___y_1855_);
    lean_dec(v___y_1854_);
    lean_dec_ref(v___y_1853_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1867_ = lean_st_ref_get(v___y_1865_);
    v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
    lean_inc_ref(v_env_1868_);
    lean_dec(v___x_1867_);
    v___x_1869_ = lean_st_ref_get(v___y_1863_);
    v_mctx_1870_ = lean_ctor_get(v___x_1869_, 0);
    lean_inc_ref(v_mctx_1870_);
    lean_dec(v___x_1869_);
    v_options_1871_ = lean_ctor_get(v___y_1864_, 2);
    v_currNamespace_1872_ = lean_ctor_get(v___y_1864_, 6);
    v_openDecls_1873_ = lean_ctor_get(v___y_1864_, 7);
    v___x_1874_ = lean_st_ref_get(v___y_1865_);
    v_ngen_1875_ = lean_ctor_get(v___x_1874_, 2);
    lean_inc_ref(v_ngen_1875_);
    lean_dec(v___x_1874_);
    v___x_1876_ = lean_box(0);
    v___x_1877_ = l_Lean_instInhabitedFileMap_default;
    lean_inc(v_openDecls_1873_);
    lean_inc(v_currNamespace_1872_);
    lean_inc_ref(v_options_1871_);
    v___x_1878_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_1878_, 0, v_env_1868_);
    lean_ctor_set(v___x_1878_, 1, v___x_1876_);
    lean_ctor_set(v___x_1878_, 2, v___x_1877_);
    lean_ctor_set(v___x_1878_, 3, v_mctx_1870_);
    lean_ctor_set(v___x_1878_, 4, v_options_1871_);
    lean_ctor_set(v___x_1878_, 5, v_currNamespace_1872_);
    lean_ctor_set(v___x_1878_, 6, v_openDecls_1873_);
    lean_ctor_set(v___x_1878_, 7, v_ngen_1875_);
    v___x_1879_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1880_, v___y_1881_, v___y_1882_);
    lean_dec(v___y_1882_);
    lean_dec_ref(v___y_1881_);
    lean_dec(v___y_1880_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_fileMap_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1894_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1890_, v___y_1891_, v___y_1892_);
                v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
                v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1894_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1897_ = v___x_1894_;
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1895_);
                    lean_dec(v___x_1894_);
                    v___x_1897_ = lean_box(0);
                    v_isShared_1898_ = v_isSharedCheck_1919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1899_ = lean_ctor_get(v___y_1891_, 1);
                v_env_1900_ = lean_ctor_get(v_a_1895_, 0);
                v_mctx_1901_ = lean_ctor_get(v_a_1895_, 3);
                v_options_1902_ = lean_ctor_get(v_a_1895_, 4);
                v_currNamespace_1903_ = lean_ctor_get(v_a_1895_, 5);
                v_openDecls_1904_ = lean_ctor_get(v_a_1895_, 6);
                v_ngen_1905_ = lean_ctor_get(v_a_1895_, 7);
                v_isSharedCheck_1916_ = (!lean_is_exclusive(v_a_1895_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v_unused_1917_ = lean_ctor_get(v_a_1895_, 2);
                    lean_dec(v_unused_1917_);
                    v_unused_1918_ = lean_ctor_get(v_a_1895_, 1);
                    lean_dec(v_unused_1918_);
                    v___x_1907_ = v_a_1895_;
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ngen_1905_);
                    lean_inc(v_openDecls_1904_);
                    lean_inc(v_currNamespace_1903_);
                    lean_inc(v_options_1902_);
                    lean_inc(v_mctx_1901_);
                    lean_inc(v_env_1900_);
                    lean_dec(v_a_1895_);
                    v___x_1907_ = lean_box(0);
                    v_isShared_1908_ = v_isSharedCheck_1916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1909_ = lean_box(0);
                lean_inc_ref(v_fileMap_1899_);
                if v_isShared_1908_ == 0 {
                    lean_ctor_set(v___x_1907_, 2, v_fileMap_1899_);
                    lean_ctor_set(v___x_1907_, 1, v___x_1909_);
                    v___x_1911_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_env_1900_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1909_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_fileMap_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_mctx_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_options_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_currNamespace_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_openDecls_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_ngen_1905_);
                    v___x_1911_ = v_reuseFailAlloc_1915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1898_ == 0 {
                    lean_ctor_set(v___x_1897_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
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
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
    lean_dec(v___y_1927_);
    lean_dec_ref(v___y_1926_);
    lean_dec(v___y_1925_);
    lean_dec_ref(v___y_1924_);
    lean_dec(v___y_1923_);
    lean_dec_ref(v___y_1922_);
    lean_dec(v___y_1921_);
    lean_dec_ref(v___y_1920_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
    mut v___y_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1939_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
                v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
                v_isSharedCheck_1949_ = (!lean_is_exclusive(v___x_1939_)) as u8;
                if v_isSharedCheck_1949_ == 0 {
                    v___x_1942_ = v___x_1939_;
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1940_);
                    lean_dec(v___x_1939_);
                    v___x_1942_ = lean_box(0);
                    v_isShared_1943_ = v_isSharedCheck_1949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1944_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1944_, 0, v_a_1940_);
                v___x_1945_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1945_, 0, v___x_1944_);
                if v_isShared_1943_ == 0 {
                    lean_ctor_set(v___x_1942_, 0, v___x_1945_);
                    v___x_1947_ = v___x_1942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
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
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1959_: *mut LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
    lean_dec(v___y_1957_);
    lean_dec_ref(v___y_1956_);
    lean_dec(v___y_1955_);
    lean_dec_ref(v___y_1954_);
    lean_dec(v___y_1953_);
    lean_dec_ref(v___y_1952_);
    lean_dec(v___y_1951_);
    lean_dec_ref(v___y_1950_);
    return v_res_1959_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_unsigned_to_nat(32);
    v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
    v___x_1962_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1962_, 0, v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = 5usize;
    v___x_1964_ = lean_unsigned_to_nat(0);
    v___x_1965_ = lean_unsigned_to_nat(32);
    v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
    v___x_1967_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
    v___x_1968_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    lean_ctor_set(v___x_1968_, 1, v___x_1966_);
    lean_ctor_set(v___x_1968_, 2, v___x_1964_);
    lean_ctor_set(v___x_1968_, 3, v___x_1964_);
    lean_ctor_set_usize(v___x_1968_, 4, v___x_1963_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(
    mut v___y_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v_enabled_1987_: u8 = 0;
    let mut v_assignment_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1971_ = lean_st_ref_get(v___y_1969_);
                v_infoState_1972_ = lean_ctor_get(v___x_1971_, 7);
                lean_inc_ref(v_infoState_1972_);
                lean_dec(v___x_1971_);
                v_trees_1973_ = lean_ctor_get(v_infoState_1972_, 2);
                lean_inc_ref(v_trees_1973_);
                lean_dec_ref(v_infoState_1972_);
                v___x_1974_ = lean_st_ref_take(v___y_1969_);
                v_infoState_1975_ = lean_ctor_get(v___x_1974_, 7);
                v_env_1976_ = lean_ctor_get(v___x_1974_, 0);
                v_nextMacroScope_1977_ = lean_ctor_get(v___x_1974_, 1);
                v_ngen_1978_ = lean_ctor_get(v___x_1974_, 2);
                v_auxDeclNGen_1979_ = lean_ctor_get(v___x_1974_, 3);
                v_traceState_1980_ = lean_ctor_get(v___x_1974_, 4);
                v_cache_1981_ = lean_ctor_get(v___x_1974_, 5);
                v_messages_1982_ = lean_ctor_get(v___x_1974_, 6);
                v_snapshotTasks_1983_ = lean_ctor_get(v___x_1974_, 8);
                v_isSharedCheck_2004_ = (!lean_is_exclusive(v___x_1974_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1985_ = v___x_1974_;
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1983_);
                    lean_inc(v_infoState_1975_);
                    lean_inc(v_messages_1982_);
                    lean_inc(v_cache_1981_);
                    lean_inc(v_traceState_1980_);
                    lean_inc(v_auxDeclNGen_1979_);
                    lean_inc(v_ngen_1978_);
                    lean_inc(v_nextMacroScope_1977_);
                    lean_inc(v_env_1976_);
                    lean_dec(v___x_1974_);
                    v___x_1985_ = lean_box(0);
                    v_isShared_1986_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1987_ = lean_ctor_get_uint8(
                    v_infoState_1975_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1988_ = lean_ctor_get(v_infoState_1975_, 0);
                v_lazyAssignment_1989_ = lean_ctor_get(v_infoState_1975_, 1);
                v_isSharedCheck_2002_ = (!lean_is_exclusive(v_infoState_1975_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = lean_ctor_get(v_infoState_1975_, 2);
                    lean_dec(v_unused_2003_);
                    v___x_1991_ = v_infoState_1975_;
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1989_);
                    lean_inc(v_assignment_1988_);
                    lean_dec(v_infoState_1975_);
                    v___x_1991_ = lean_box(0);
                    v_isShared_1992_ = v_isSharedCheck_2002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1993_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
                if v_isShared_1992_ == 0 {
                    lean_ctor_set(v___x_1991_, 2, v___x_1993_);
                    v___x_1995_ = v___x_1991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_assignment_1988_);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_lazyAssignment_1989_);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 2, v___x_1993_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2001_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1987_,
                    );
                    v___x_1995_ = v_reuseFailAlloc_2001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1986_ == 0 {
                    lean_ctor_set(v___x_1985_, 7, v___x_1995_);
                    v___x_1997_ = v___x_1985_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_env_1976_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_nextMacroScope_1977_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_ngen_1978_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_auxDeclNGen_1979_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_traceState_1980_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 5, v_cache_1981_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 6, v_messages_1982_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 7, v___x_1995_);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 8, v_snapshotTasks_1983_);
                    v___x_1997_ = v_reuseFailAlloc_2000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1998_ = lean_st_ref_set(v___y_1969_, v___x_1997_);
                v___x_1999_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1999_, 0, v_trees_1973_);
                return v___x_1999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2005_);
    lean_dec(v___y_2005_);
    return v_res_2007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(
    mut v___x_2008_: *mut LeanObject,
    mut v_ctx_x3f_2009_: *mut LeanObject,
    mut v_sz_2010_: usize,
    mut v_i_2011_: usize,
    mut v_bs_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: usize = 0;
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2022_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
                if v___x_2022_ == 0 {
                    lean_dec_ref(v_ctx_x3f_2009_);
                    v___x_2023_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2023_, 0, v_bs_2012_);
                    return v___x_2023_;
                } else {
                    v_assignment_2024_ = lean_ctor_get(v___x_2008_, 0);
                    lean_inc_ref(v_ctx_x3f_2009_);
                    lean_inc(v___y_2020_);
                    lean_inc_ref(v___y_2019_);
                    lean_inc(v___y_2018_);
                    lean_inc_ref(v___y_2017_);
                    lean_inc(v___y_2016_);
                    lean_inc_ref(v___y_2015_);
                    lean_inc(v___y_2014_);
                    lean_inc_ref(v___y_2013_);
                    v___x_2025_ = lean_apply_9(
                        v_ctx_x3f_2009_,
                        v___y_2013_,
                        v___y_2014_,
                        v___y_2015_,
                        v___y_2016_,
                        v___y_2017_,
                        v___y_2018_,
                        v___y_2019_,
                        v___y_2020_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2025_) == 0 {
                        v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
                        lean_inc(v_a_2026_);
                        lean_dec_ref_known(v___x_2025_, 1);
                        v_v_2027_ = lean_array_uget(v_bs_2012_, v_i_2011_);
                        v___x_2028_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2029_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2028_);
                        v_tree_2036_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_2027_, v_assignment_2024_);
                        if lean_obj_tag(v_a_2026_) == 0 {
                            v_a_2031_ = v_tree_2036_;
                            state = 1;
                            continue;
                        } else {
                            v_val_2037_ = lean_ctor_get(v_a_2026_, 0);
                            lean_inc(v_val_2037_);
                            lean_dec_ref_known(v_a_2026_, 1);
                            v___x_2038_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2038_, 0, v_val_2037_);
                            lean_ctor_set(v___x_2038_, 1, v_tree_2036_);
                            v_a_2031_ = v___x_2038_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_bs_2012_);
                        lean_dec_ref(v_ctx_x3f_2009_);
                        v_a_2039_ = lean_ctor_get(v___x_2025_, 0);
                        v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2025_)) as u8;
                        if v_isSharedCheck_2046_ == 0 {
                            v___x_2041_ = v___x_2025_;
                            v_isShared_2042_ = v_isSharedCheck_2046_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2039_);
                            lean_dec(v___x_2025_);
                            v___x_2041_ = lean_box(0);
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
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
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
    mut v___x_2047_: *mut LeanObject,
    mut v_ctx_x3f_2048_: *mut LeanObject,
    mut v_sz_2049_: *mut LeanObject,
    mut v_i_2050_: *mut LeanObject,
    mut v_bs_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2061_: usize = 0;
    let mut v_i_boxed_2062_: usize = 0;
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2061_ = lean_unbox_usize(v_sz_2049_);
    lean_dec(v_sz_2049_);
    v_i_boxed_2062_ = lean_unbox_usize(v_i_2050_);
    lean_dec(v_i_2050_);
    v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2047_, v_ctx_x3f_2048_, v_sz_boxed_2061_, v_i_boxed_2062_, v_bs_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
    lean_dec(v___y_2059_);
    lean_dec_ref(v___y_2058_);
    lean_dec(v___y_2057_);
    lean_dec_ref(v___y_2056_);
    lean_dec(v___y_2055_);
    lean_dec_ref(v___y_2054_);
    lean_dec(v___y_2053_);
    lean_dec_ref(v___y_2052_);
    lean_dec_ref(v___x_2047_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(
    mut v___x_2064_: *mut LeanObject,
    mut v_ctx_x3f_2065_: *mut LeanObject,
    mut v_x_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v_sz_2080_: usize = 0;
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2086_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_a_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_vs_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_sz_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_a_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2066_) == 0 {
                    v_cs_2076_ = lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2102_ = (!lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2102_ == 0 {
                        v___x_2078_ = v_x_2066_;
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_2076_);
                        lean_dec(v_x_2066_);
                        v___x_2078_ = lean_box(0);
                        v_isShared_2079_ = v_isSharedCheck_2102_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2103_ = lean_ctor_get(v_x_2066_, 0);
                    v_isSharedCheck_2129_ = (!lean_is_exclusive(v_x_2066_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2105_ = v_x_2066_;
                        v_isShared_2106_ = v_isSharedCheck_2129_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_vs_2103_);
                        lean_dec(v_x_2066_);
                        v___x_2105_ = lean_box(0);
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
                if lean_obj_tag(v___x_2082_) == 0 {
                    v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2093_ = (!lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2093_ == 0 {
                        v___x_2085_ = v___x_2082_;
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2083_);
                        lean_dec(v___x_2082_);
                        v___x_2085_ = lean_box(0);
                        v_isShared_2086_ = v_isSharedCheck_2093_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2078_);
                    v_a_2094_ = lean_ctor_get(v___x_2082_, 0);
                    v_isSharedCheck_2101_ = (!lean_is_exclusive(v___x_2082_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2096_ = v___x_2082_;
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2094_);
                        lean_dec(v___x_2082_);
                        v___x_2096_ = lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2101_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2079_ == 0 {
                    lean_ctor_set(v___x_2078_, 0, v_a_2083_);
                    v___x_2088_ = v___x_2078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2083_);
                    v___x_2088_ = v_reuseFailAlloc_2092_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2086_ == 0 {
                    lean_ctor_set(v___x_2085_, 0, v___x_2088_);
                    v___x_2090_ = v___x_2085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
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
                    v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
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
                if lean_obj_tag(v___x_2109_) == 0 {
                    v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2120_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2120_ == 0 {
                        v___x_2112_ = v___x_2109_;
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2110_);
                        lean_dec(v___x_2109_);
                        v___x_2112_ = lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2105_);
                    v_a_2121_ = lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2128_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2128_ == 0 {
                        v___x_2123_ = v___x_2109_;
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2121_);
                        lean_dec(v___x_2109_);
                        v___x_2123_ = lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2128_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2106_ == 0 {
                    lean_ctor_set(v___x_2105_, 0, v_a_2110_);
                    v___x_2115_ = v___x_2105_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2119_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2113_ == 0 {
                    lean_ctor_set(v___x_2112_, 0, v___x_2115_);
                    v___x_2117_ = v___x_2112_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
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
                    v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
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
    mut v___x_2130_: *mut LeanObject,
    mut v_ctx_x3f_2131_: *mut LeanObject,
    mut v_sz_2132_: usize,
    mut v_i_2133_: usize,
    mut v_bs_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v___y_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2144_ = lean_usize_dec_lt(v_i_2133_, v_sz_2132_);
                if v___x_2144_ == 0 {
                    lean_dec_ref(v_ctx_x3f_2131_);
                    v___x_2145_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2145_, 0, v_bs_2134_);
                    return v___x_2145_;
                } else {
                    v_v_2146_ = lean_array_uget_borrowed(v_bs_2134_, v_i_2133_);
                    lean_inc(v_v_2146_);
                    lean_inc_ref(v_ctx_x3f_2131_);
                    v___x_2147_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2130_, v_ctx_x3f_2131_, v_v_2146_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
                    if lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
                        lean_inc(v_a_2148_);
                        lean_dec_ref_known(v___x_2147_, 1);
                        v___x_2149_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2150_ = lean_array_uset(v_bs_2134_, v_i_2133_, v___x_2149_);
                        v___x_2151_ = 1usize;
                        v___x_2152_ = lean_usize_add(v_i_2133_, v___x_2151_);
                        v___x_2153_ = lean_array_uset(v_bs_x27_2150_, v_i_2133_, v_a_2148_);
                        v_i_2133_ = v___x_2152_;
                        v_bs_2134_ = v___x_2153_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2134_);
                        lean_dec_ref(v_ctx_x3f_2131_);
                        v_a_2155_ = lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2162_ = (!lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2147_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2155_);
                            lean_dec(v___x_2147_);
                            v___x_2157_ = lean_box(0);
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
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
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
    mut v___x_2163_: *mut LeanObject,
    mut v_ctx_x3f_2164_: *mut LeanObject,
    mut v_sz_2165_: *mut LeanObject,
    mut v_i_2166_: *mut LeanObject,
    mut v_bs_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
    mut v___y_2175_: *mut LeanObject,
    mut v___y_2176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2177_: usize = 0;
    let mut v_i_boxed_2178_: usize = 0;
    let mut v_res_2179_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2177_ = lean_unbox_usize(v_sz_2165_);
    lean_dec(v_sz_2165_);
    v_i_boxed_2178_ = lean_unbox_usize(v_i_2166_);
    lean_dec(v_i_2166_);
    v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_2163_, v_ctx_x3f_2164_, v_sz_boxed_2177_, v_i_boxed_2178_, v_bs_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
    lean_dec(v___y_2175_);
    lean_dec_ref(v___y_2174_);
    lean_dec(v___y_2173_);
    lean_dec_ref(v___y_2172_);
    lean_dec(v___y_2171_);
    lean_dec_ref(v___y_2170_);
    lean_dec(v___y_2169_);
    lean_dec_ref(v___y_2168_);
    lean_dec_ref(v___x_2163_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(
    mut v___x_2180_: *mut LeanObject,
    mut v_ctx_x3f_2181_: *mut LeanObject,
    mut v_x_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v___y_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2192_: *mut LeanObject = core::ptr::null_mut();
    v_res_2192_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2180_, v_ctx_x3f_2181_, v_x_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
    lean_dec(v___y_2190_);
    lean_dec_ref(v___y_2189_);
    lean_dec(v___y_2188_);
    lean_dec_ref(v___y_2187_);
    lean_dec(v___y_2186_);
    lean_dec_ref(v___y_2185_);
    lean_dec(v___y_2184_);
    lean_dec_ref(v___y_2183_);
    lean_dec_ref(v___x_2180_);
    return v_res_2192_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(
    mut v___x_2193_: *mut LeanObject,
    mut v_ctx_x3f_2194_: *mut LeanObject,
    mut v_t_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_2208_: usize = 0;
    let mut v_tailOff_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2215_: usize = 0;
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_a_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_a_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2205_ = lean_ctor_get(v_t_2195_, 0);
                v_tail_2206_ = lean_ctor_get(v_t_2195_, 1);
                v_size_2207_ = lean_ctor_get(v_t_2195_, 2);
                v_shift_2208_ = lean_ctor_get_usize(v_t_2195_, 4);
                v_tailOff_2209_ = lean_ctor_get(v_t_2195_, 3);
                v_isSharedCheck_2245_ = (!lean_is_exclusive(v_t_2195_)) as u8;
                if v_isSharedCheck_2245_ == 0 {
                    v___x_2211_ = v_t_2195_;
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_2209_);
                    lean_inc(v_size_2207_);
                    lean_inc(v_tail_2206_);
                    lean_inc(v_root_2205_);
                    lean_dec(v_t_2195_);
                    v___x_2211_ = lean_box(0);
                    v_isShared_2212_ = v_isSharedCheck_2245_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_ctx_x3f_2194_);
                v___x_2213_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_2193_, v_ctx_x3f_2194_, v_root_2205_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                if lean_obj_tag(v___x_2213_) == 0 {
                    v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
                    lean_inc(v_a_2214_);
                    lean_dec_ref_known(v___x_2213_, 1);
                    v_sz_2215_ = lean_array_size(v_tail_2206_);
                    v___x_2216_ = 0usize;
                    v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_2193_, v_ctx_x3f_2194_, v_sz_2215_, v___x_2216_, v_tail_2206_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
                    if lean_obj_tag(v___x_2217_) == 0 {
                        v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2228_ = (!lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2228_ == 0 {
                            v___x_2220_ = v___x_2217_;
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2218_);
                            lean_dec(v___x_2217_);
                            v___x_2220_ = lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2228_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2214_);
                        lean_del_object(v___x_2211_);
                        lean_dec(v_tailOff_2209_);
                        lean_dec(v_size_2207_);
                        v_a_2229_ = lean_ctor_get(v___x_2217_, 0);
                        v_isSharedCheck_2236_ = (!lean_is_exclusive(v___x_2217_)) as u8;
                        if v_isSharedCheck_2236_ == 0 {
                            v___x_2231_ = v___x_2217_;
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2229_);
                            lean_dec(v___x_2217_);
                            v___x_2231_ = lean_box(0);
                            v_isShared_2232_ = v_isSharedCheck_2236_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2211_);
                    lean_dec(v_tailOff_2209_);
                    lean_dec(v_size_2207_);
                    lean_dec_ref(v_tail_2206_);
                    lean_dec_ref(v_ctx_x3f_2194_);
                    v_a_2237_ = lean_ctor_get(v___x_2213_, 0);
                    v_isSharedCheck_2244_ = (!lean_is_exclusive(v___x_2213_)) as u8;
                    if v_isSharedCheck_2244_ == 0 {
                        v___x_2239_ = v___x_2213_;
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2237_);
                        lean_dec(v___x_2213_);
                        v___x_2239_ = lean_box(0);
                        v_isShared_2240_ = v_isSharedCheck_2244_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2212_ == 0 {
                    lean_ctor_set(v___x_2211_, 1, v_a_2218_);
                    lean_ctor_set(v___x_2211_, 0, v_a_2214_);
                    v___x_2223_ = v___x_2211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2214_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2218_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_size_2207_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_tailOff_2209_);
                    lean_ctor_set_usize(v_reuseFailAlloc_2227_, 4, v_shift_2208_);
                    v___x_2223_ = v_reuseFailAlloc_2227_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2221_ == 0 {
                    lean_ctor_set(v___x_2220_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
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
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
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
                    v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
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
    mut v___x_2246_: *mut LeanObject,
    mut v_ctx_x3f_2247_: *mut LeanObject,
    mut v_t_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2258_: *mut LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_2246_, v_ctx_x3f_2247_, v_t_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
    lean_dec(v___y_2256_);
    lean_dec_ref(v___y_2255_);
    lean_dec(v___y_2254_);
    lean_dec_ref(v___y_2253_);
    lean_dec(v___y_2252_);
    lean_dec_ref(v___y_2251_);
    lean_dec(v___y_2250_);
    lean_dec_ref(v___y_2249_);
    lean_dec_ref(v___x_2246_);
    return v_res_2258_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(
    mut v___y_2259_: *mut LeanObject,
    mut v_ctx_x3f_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
    mut v_a_x3f_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_enabled_2292_: u8 = 0;
    let mut v_assignment_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2271_ = lean_st_ref_get(v___y_2259_);
                v_infoState_2272_ = lean_ctor_get(v___x_2271_, 7);
                lean_inc_ref(v_infoState_2272_);
                lean_dec(v___x_2271_);
                v_trees_2273_ = lean_ctor_get(v_infoState_2272_, 2);
                lean_inc_ref(v_trees_2273_);
                v___x_2274_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_2272_, v_ctx_x3f_2260_, v_trees_2273_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2259_);
                lean_dec_ref(v_infoState_2272_);
                if lean_obj_tag(v___x_2274_) == 0 {
                    v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2313_ = (!lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2313_ == 0 {
                        v___x_2277_ = v___x_2274_;
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2275_);
                        lean_dec(v___x_2274_);
                        v___x_2277_ = lean_box(0);
                        v_isShared_2278_ = v_isSharedCheck_2313_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_2268_);
                    v_a_2314_ = lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2321_ = (!lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2274_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2314_);
                        lean_dec(v___x_2274_);
                        v___x_2316_ = lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2279_ = lean_st_ref_take(v___y_2259_);
                v_infoState_2280_ = lean_ctor_get(v___x_2279_, 7);
                v_env_2281_ = lean_ctor_get(v___x_2279_, 0);
                v_nextMacroScope_2282_ = lean_ctor_get(v___x_2279_, 1);
                v_ngen_2283_ = lean_ctor_get(v___x_2279_, 2);
                v_auxDeclNGen_2284_ = lean_ctor_get(v___x_2279_, 3);
                v_traceState_2285_ = lean_ctor_get(v___x_2279_, 4);
                v_cache_2286_ = lean_ctor_get(v___x_2279_, 5);
                v_messages_2287_ = lean_ctor_get(v___x_2279_, 6);
                v_snapshotTasks_2288_ = lean_ctor_get(v___x_2279_, 8);
                v_isSharedCheck_2312_ = (!lean_is_exclusive(v___x_2279_)) as u8;
                if v_isSharedCheck_2312_ == 0 {
                    v___x_2290_ = v___x_2279_;
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2288_);
                    lean_inc(v_infoState_2280_);
                    lean_inc(v_messages_2287_);
                    lean_inc(v_cache_2286_);
                    lean_inc(v_traceState_2285_);
                    lean_inc(v_auxDeclNGen_2284_);
                    lean_inc(v_ngen_2283_);
                    lean_inc(v_nextMacroScope_2282_);
                    lean_inc(v_env_2281_);
                    lean_dec(v___x_2279_);
                    v___x_2290_ = lean_box(0);
                    v_isShared_2291_ = v_isSharedCheck_2312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_2292_ = lean_ctor_get_uint8(
                    v_infoState_2280_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_2293_ = lean_ctor_get(v_infoState_2280_, 0);
                v_lazyAssignment_2294_ = lean_ctor_get(v_infoState_2280_, 1);
                v_isSharedCheck_2310_ = (!lean_is_exclusive(v_infoState_2280_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v_unused_2311_ = lean_ctor_get(v_infoState_2280_, 2);
                    lean_dec(v_unused_2311_);
                    v___x_2296_ = v_infoState_2280_;
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_2294_);
                    lean_inc(v_assignment_2293_);
                    lean_dec(v_infoState_2280_);
                    v___x_2296_ = lean_box(0);
                    v_isShared_2297_ = v_isSharedCheck_2310_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2298_ = l_Lean_PersistentArray_append___redArg(v_a_2268_, v_a_2275_);
                lean_dec(v_a_2275_);
                if v_isShared_2297_ == 0 {
                    lean_ctor_set(v___x_2296_, 2, v___x_2298_);
                    v___x_2300_ = v___x_2296_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_assignment_2293_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_lazyAssignment_2294_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 2, v___x_2298_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2309_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_2292_,
                    );
                    v___x_2300_ = v_reuseFailAlloc_2309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2291_ == 0 {
                    lean_ctor_set(v___x_2290_, 7, v___x_2300_);
                    v___x_2302_ = v___x_2290_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_env_2281_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2282_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2283_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2284_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2285_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_cache_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 6, v_messages_2287_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 7, v___x_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2288_);
                    v___x_2302_ = v_reuseFailAlloc_2308_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2303_ = lean_st_ref_set(v___y_2259_, v___x_2302_);
                v___x_2304_ = lean_box(0);
                if v_isShared_2278_ == 0 {
                    lean_ctor_set(v___x_2277_, 0, v___x_2304_);
                    v___x_2306_ = v___x_2277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
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
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
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
    mut v___y_2322_: *mut LeanObject,
    mut v_ctx_x3f_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
    mut v_a_x3f_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2334_: *mut LeanObject = core::ptr::null_mut();
    v_res_2334_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2322_, v_ctx_x3f_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v_a_2331_, v_a_x3f_2332_);
    lean_dec(v_a_x3f_2332_);
    lean_dec_ref(v___y_2330_);
    lean_dec(v___y_2329_);
    lean_dec_ref(v___y_2328_);
    lean_dec(v___y_2327_);
    lean_dec_ref(v___y_2326_);
    lean_dec(v___y_2325_);
    lean_dec_ref(v___y_2324_);
    lean_dec(v___y_2322_);
    return v_res_2334_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(
    mut v_x_2335_: *mut LeanObject,
    mut v_ctx_x3f_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2348_: u8 = 0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2371_: u8 = 0;
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_reuseFailAlloc_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_a_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_unused_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_st_ref_get(v___y_2344_);
                v_infoState_2347_ = lean_ctor_get(v___x_2346_, 7);
                lean_inc_ref(v_infoState_2347_);
                lean_dec(v___x_2346_);
                v_enabled_2348_ = lean_ctor_get_uint8(
                    v_infoState_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_2347_);
                if v_enabled_2348_ == 0 {
                    lean_dec_ref(v_ctx_x3f_2336_);
                    lean_inc(v___y_2344_);
                    lean_inc_ref(v___y_2343_);
                    lean_inc(v___y_2342_);
                    lean_inc_ref(v___y_2341_);
                    lean_inc(v___y_2340_);
                    lean_inc_ref(v___y_2339_);
                    lean_inc(v___y_2338_);
                    lean_inc_ref(v___y_2337_);
                    v___x_2349_ = lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        lean_box(0),
                    );
                    return v___x_2349_;
                } else {
                    v___x_2350_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2344_);
                    v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
                    lean_inc(v_a_2351_);
                    lean_dec_ref(v___x_2350_);
                    lean_inc(v___y_2344_);
                    lean_inc_ref(v___y_2343_);
                    lean_inc(v___y_2342_);
                    lean_inc_ref(v___y_2341_);
                    lean_inc(v___y_2340_);
                    lean_inc_ref(v___y_2339_);
                    lean_inc(v___y_2338_);
                    lean_inc_ref(v___y_2337_);
                    v_r_2352_ = lean_apply_9(
                        v_x_2335_,
                        v___y_2337_,
                        v___y_2338_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                        v___y_2344_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_2352_) == 0 {
                        v_a_2353_ = lean_ctor_get(v_r_2352_, 0);
                        v_isSharedCheck_2377_ = (!lean_is_exclusive(v_r_2352_)) as u8;
                        if v_isSharedCheck_2377_ == 0 {
                            v___x_2355_ = v_r_2352_;
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2353_);
                            lean_dec(v_r_2352_);
                            v___x_2355_ = lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2377_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2378_ = lean_ctor_get(v_r_2352_, 0);
                        lean_inc(v_a_2378_);
                        lean_dec_ref_known(v_r_2352_, 1);
                        v___x_2379_ = lean_box(0);
                        v___x_2380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2379_);
                        if lean_obj_tag(v___x_2380_) == 0 {
                            v_isSharedCheck_2387_ = (!lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2387_ == 0 {
                                v_unused_2388_ = lean_ctor_get(v___x_2380_, 0);
                                lean_dec(v_unused_2388_);
                                v___x_2382_ = v___x_2380_;
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_2380_);
                                v___x_2382_ = lean_box(0);
                                v_isShared_2383_ = v_isSharedCheck_2387_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2378_);
                            v_a_2389_ = lean_ctor_get(v___x_2380_, 0);
                            v_isSharedCheck_2396_ = (!lean_is_exclusive(v___x_2380_)) as u8;
                            if v_isSharedCheck_2396_ == 0 {
                                v___x_2391_ = v___x_2380_;
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2389_);
                                lean_dec(v___x_2380_);
                                v___x_2391_ = lean_box(0);
                                v_isShared_2392_ = v_isSharedCheck_2396_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_2353_);
                if v_isShared_2356_ == 0 {
                    lean_ctor_set_tag(v___x_2355_, 1);
                    v___x_2358_ = v___x_2355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_2344_, v_ctx_x3f_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v_a_2351_, v___x_2358_);
                lean_dec_ref(v___x_2358_);
                if lean_obj_tag(v___x_2359_) == 0 {
                    v_isSharedCheck_2366_ = (!lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v_unused_2367_ = lean_ctor_get(v___x_2359_, 0);
                        lean_dec(v_unused_2367_);
                        v___x_2361_ = v___x_2359_;
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2359_);
                        v___x_2361_ = lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2353_);
                    v_a_2368_ = lean_ctor_get(v___x_2359_, 0);
                    v_isSharedCheck_2375_ = (!lean_is_exclusive(v___x_2359_)) as u8;
                    if v_isSharedCheck_2375_ == 0 {
                        v___x_2370_ = v___x_2359_;
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2368_);
                        lean_dec(v___x_2359_);
                        v___x_2370_ = lean_box(0);
                        v_isShared_2371_ = v_isSharedCheck_2375_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2362_ == 0 {
                    lean_ctor_set(v___x_2361_, 0, v_a_2353_);
                    v___x_2364_ = v___x_2361_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2353_);
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
                    v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
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
                    lean_ctor_set_tag(v___x_2382_, 1);
                    lean_ctor_set(v___x_2382_, 0, v_a_2378_);
                    v___x_2385_ = v___x_2382_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
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
                    v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
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
    mut v_x_2397_: *mut LeanObject,
    mut v_ctx_x3f_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2408_: *mut LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2397_, v_ctx_x3f_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
    lean_dec(v___y_2406_);
    lean_dec_ref(v___y_2405_);
    lean_dec(v___y_2404_);
    lean_dec_ref(v___y_2403_);
    lean_dec(v___y_2402_);
    lean_dec_ref(v___y_2401_);
    lean_dec(v___y_2400_);
    lean_dec_ref(v___y_2399_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(
    mut v_x_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    v___f_2420_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0;
    v___x_2421_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2410_, v___f_2420_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(
    mut v_x_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2432_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2430_);
    lean_dec_ref(v___y_2429_);
    lean_dec(v___y_2428_);
    lean_dec_ref(v___y_2427_);
    lean_dec(v___y_2426_);
    lean_dec_ref(v___y_2425_);
    lean_dec(v___y_2424_);
    lean_dec_ref(v___y_2423_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(
    mut v_00_u03b1_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
    mut v___y_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2445_: *mut LeanObject,
    mut v_x_2446_: *mut LeanObject,
    mut v___y_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
    mut v___y_2451_: *mut LeanObject,
    mut v___y_2452_: *mut LeanObject,
    mut v___y_2453_: *mut LeanObject,
    mut v___y_2454_: *mut LeanObject,
    mut v___y_2455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2456_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2454_);
    lean_dec_ref(v___y_2453_);
    lean_dec(v___y_2452_);
    lean_dec_ref(v___y_2451_);
    lean_dec(v___y_2450_);
    lean_dec_ref(v___y_2449_);
    lean_dec(v___y_2448_);
    lean_dec_ref(v___y_2447_);
    return v_res_2456_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalClassical(
    mut v_stx_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_a_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_unsigned_to_nat(1);
    v___x_2469_ = l_Lean_Elab_Tactic_evalClassical___closed__0;
    v___x_2470_ = lean_alloc_closure(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed as *mut core::ffi::c_void, 13, 4);
    lean_closure_set(v___x_2470_, 0, lean_box(0));
    lean_closure_set(v___x_2470_, 1, v___x_2468_);
    lean_closure_set(v___x_2470_, 2, v___x_2469_);
    lean_closure_set(v___x_2470_, 3, v_stx_2458_);
    v___x_2471_ = lean_alloc_closure(
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___x_2471_, 0, lean_box(0));
    lean_closure_set(v___x_2471_, 1, v___x_2470_);
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
    mut v_stx_2473_: *mut LeanObject,
    mut v_a_2474_: *mut LeanObject,
    mut v_a_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
    mut v_a_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
    mut v_a_2481_: *mut LeanObject,
    mut v_a_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2483_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2481_);
    lean_dec_ref(v_a_2480_);
    lean_dec(v_a_2479_);
    lean_dec_ref(v_a_2478_);
    lean_dec(v_a_2477_);
    lean_dec_ref(v_a_2476_);
    lean_dec(v_a_2475_);
    lean_dec_ref(v_a_2474_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2484_: *mut LeanObject,
    mut v_stx_2485_: *mut LeanObject,
    mut v_act_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_2485_, v_act_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2497_: *mut LeanObject,
    mut v_stx_2498_: *mut LeanObject,
    mut v_act_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_2497_, v_stx_2498_, v_act_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
    lean_dec(v___y_2507_);
    lean_dec_ref(v___y_2506_);
    lean_dec(v___y_2505_);
    lean_dec_ref(v___y_2504_);
    lean_dec(v___y_2503_);
    lean_dec_ref(v___y_2502_);
    lean_dec(v___y_2501_);
    lean_dec_ref(v___y_2500_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(
    mut v_00_u03b1_2510_: *mut LeanObject,
    mut v_split_2511_: *mut LeanObject,
    mut v_act_2512_: *mut LeanObject,
    mut v_stx_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    v___x_2523_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_2511_, v_act_2512_, v_stx_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
    return v___x_2523_;
}
pub unsafe fn l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(
    mut v_00_u03b1_2524_: *mut LeanObject,
    mut v_split_2525_: *mut LeanObject,
    mut v_act_2526_: *mut LeanObject,
    mut v_stx_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_res_2537_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_2524_, v_split_2525_, v_act_2526_, v_stx_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
    lean_dec(v___y_2535_);
    lean_dec_ref(v___y_2534_);
    lean_dec(v___y_2533_);
    lean_dec_ref(v___y_2532_);
    lean_dec(v___y_2531_);
    lean_dec_ref(v___y_2530_);
    lean_dec(v___y_2529_);
    lean_dec_ref(v___y_2528_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_2543_, v___y_2544_, v___y_2545_);
    return v___x_2547_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(
    mut v___y_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
    lean_dec(v___y_2555_);
    lean_dec_ref(v___y_2554_);
    lean_dec(v___y_2553_);
    lean_dec_ref(v___y_2552_);
    lean_dec(v___y_2551_);
    lean_dec_ref(v___y_2550_);
    lean_dec(v___y_2549_);
    lean_dec_ref(v___y_2548_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(
    mut v___y_2558_: *mut LeanObject,
    mut v___y_2559_: *mut LeanObject,
    mut v___y_2560_: *mut LeanObject,
    mut v___y_2561_: *mut LeanObject,
    mut v___y_2562_: *mut LeanObject,
    mut v___y_2563_: *mut LeanObject,
    mut v___y_2564_: *mut LeanObject,
    mut v___y_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2567_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_2565_);
    return v___x_2567_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(
    mut v___y_2568_: *mut LeanObject,
    mut v___y_2569_: *mut LeanObject,
    mut v___y_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
    mut v___y_2575_: *mut LeanObject,
    mut v___y_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    lean_dec(v___y_2575_);
    lean_dec_ref(v___y_2574_);
    lean_dec(v___y_2573_);
    lean_dec_ref(v___y_2572_);
    lean_dec(v___y_2571_);
    lean_dec_ref(v___y_2570_);
    lean_dec(v___y_2569_);
    lean_dec_ref(v___y_2568_);
    return v_res_2577_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(
    mut v_00_u03b1_2578_: *mut LeanObject,
    mut v_x_2579_: *mut LeanObject,
    mut v_ctx_x3f_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
    mut v___y_2583_: *mut LeanObject,
    mut v___y_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
    mut v___y_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    v___x_2590_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_2579_, v_ctx_x3f_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
    return v___x_2590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(
    mut v_00_u03b1_2591_: *mut LeanObject,
    mut v_x_2592_: *mut LeanObject,
    mut v_ctx_x3f_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
    mut v___y_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2603_: *mut LeanObject = core::ptr::null_mut();
    v_res_2603_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_2591_, v_x_2592_, v_ctx_x3f_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
    lean_dec(v___y_2601_);
    lean_dec_ref(v___y_2600_);
    lean_dec(v___y_2599_);
    lean_dec_ref(v___y_2598_);
    lean_dec(v___y_2597_);
    lean_dec_ref(v___y_2596_);
    lean_dec(v___y_2595_);
    lean_dec_ref(v___y_2594_);
    return v_res_2603_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1()
-> *mut LeanObject {
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    v___x_2621_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2622_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4;
    v___x_2623_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2624_ = lean_alloc_closure(
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
    mut v_a_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    return v_res_2627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3()
-> *mut LeanObject {
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    v___x_2629_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7;
    v___x_2630_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_2629_);
    return v___x_2630_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(
    mut v_a_2631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2632_: *mut LeanObject = core::ptr::null_mut();
    v_res_2632_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    return v_res_2632_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Classical(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Classical(builtin);
}
