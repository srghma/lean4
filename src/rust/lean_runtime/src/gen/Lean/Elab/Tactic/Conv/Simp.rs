// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Simp
// Imports: Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv.Basic Lean.Elab.Tactic.SimpTrace
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray3___redArg, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node6,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, l_Lean_Elab_Tactic_Conv_updateLhs,
    runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg, l_Lean_Elab_Tactic_mkSimpContext,
};
use crate::r#gen::Lean::Elab::Tactic::SimpTrace::{
    initialize_Lean_Elab_Tactic_SimpTrace, l_Lean_Elab_Tactic_mkSimpCallStx,
    runtime_initialize_Lean_Elab_Tactic_SimpTrace,
};
use crate::r#gen::Lean::Elab::Tactic::Split::{
    initialize_Lean_Elab_Tactic_Split, runtime_initialize_Lean_Elab_Tactic_Split,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_nil;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSimpTheorems___boxed;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{l_Lean_Meta_dsimp, l_Lean_Meta_simp};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
use crate::r#gen::Lean::Meta::Tactic::Split::l_Lean_Meta_Split_simpMatch;
use crate::r#gen::Lean::Meta::Tactic::TryThis::l_Lean_Meta_Tactic_TryThis_addSuggestion;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_usize,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_getSimpTheorems___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value) as *mut LeanObject,14621726445050439147 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value) as *mut LeanObject,13351543798210616694 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value: LeanStringObject<7> =
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
        m_data: [116, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value)
                as *mut LeanObject,
            16145843736367156323 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value: LeanStringObject<10> =
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
        m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value: LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value: LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value: LeanStringObject<5> =
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
        m_data: [111, 110, 108, 121, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value: LeanStringObject<9> =
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
        m_data: [115, 105, 109, 112, 65, 114, 103, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value: LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value)
                as *mut LeanObject,
            4033974689118230740 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value) as *mut LeanObject,16766288616492194285 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value) as *mut LeanObject,2709596213829771159 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value) as *mut LeanObject,13624115421224297802 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value) as *mut LeanObject,682381425026147175 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value) as *mut LeanObject,5014538692942607590 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value) as *mut LeanObject,((( 61 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value: LeanStringObject<10> =
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
        m_data: [100, 115, 105, 109, 112, 65, 114, 103, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value)
                as *mut LeanObject,
            1408925737459485508 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 68, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value) as *mut LeanObject,7214738609362602633 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Conv_applySimpResult(
    mut v_result_1211_: *mut LeanObject,
    mut v_a_1212_: *mut LeanObject,
    mut v_a_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
    mut v_a_1215_: *mut LeanObject,
    mut v_a_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_a_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_proof_x3f_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_x3f_1221_ = lean_ctor_get(v_result_1211_, 1);
                if lean_obj_tag(v_proof_x3f_1221_) == 0 {
                    v_expr_1222_ = lean_ctor_get(v_result_1211_, 0);
                    lean_inc_ref(v_expr_1222_);
                    lean_dec_ref(v_result_1211_);
                    v___x_1223_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                        v_expr_1222_,
                        v_a_1212_,
                        v_a_1213_,
                        v_a_1214_,
                        v_a_1215_,
                        v_a_1216_,
                        v_a_1217_,
                        v_a_1218_,
                        v_a_1219_,
                    );
                    return v___x_1223_;
                } else {
                    v_expr_1224_ = lean_ctor_get(v_result_1211_, 0);
                    lean_inc_ref(v_expr_1224_);
                    v___x_1225_ = l_Lean_Meta_Simp_Result_getProof(
                        v_result_1211_,
                        v_a_1216_,
                        v_a_1217_,
                        v_a_1218_,
                        v_a_1219_,
                    );
                    if lean_obj_tag(v___x_1225_) == 0 {
                        v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
                        lean_inc(v_a_1226_);
                        lean_dec_ref_known(v___x_1225_, 1);
                        v___x_1227_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                            v_expr_1224_,
                            v_a_1226_,
                            v_a_1212_,
                            v_a_1213_,
                            v_a_1214_,
                            v_a_1215_,
                            v_a_1216_,
                            v_a_1217_,
                            v_a_1218_,
                            v_a_1219_,
                        );
                        return v___x_1227_;
                    } else {
                        lean_dec_ref(v_expr_1224_);
                        v_a_1228_ = lean_ctor_get(v___x_1225_, 0);
                        v_isSharedCheck_1235_ = (!lean_is_exclusive(v___x_1225_)) as u8;
                        if v_isSharedCheck_1235_ == 0 {
                            v___x_1230_ = v___x_1225_;
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1228_);
                            lean_dec(v___x_1225_);
                            v___x_1230_ = lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1231_ == 0 {
                    v___x_1233_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
                    v___x_1233_ = v_reuseFailAlloc_1234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(
    mut v_result_1236_: *mut LeanObject,
    mut v_a_1237_: *mut LeanObject,
    mut v_a_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
    mut v_a_1242_: *mut LeanObject,
    mut v_a_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1246_: *mut LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
        v_result_1236_,
        v_a_1237_,
        v_a_1238_,
        v_a_1239_,
        v_a_1240_,
        v_a_1241_,
        v_a_1242_,
        v_a_1243_,
        v_a_1244_,
    );
    lean_dec(v_a_1244_);
    lean_dec_ref(v_a_1243_);
    lean_dec(v_a_1242_);
    lean_dec_ref(v_a_1241_);
    lean_dec(v_a_1240_);
    lean_dec_ref(v_a_1239_);
    lean_dec(v_a_1238_);
    lean_dec_ref(v_a_1237_);
    return v_res_1246_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1247_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    v___x_1248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0,
    );
    v___x_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1249_, 0, v___x_1248_);
    return v___x_1249_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = lean_unsigned_to_nat(0);
    v___x_1251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    v___x_1252_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1252_, 0, v___x_1251_);
    lean_ctor_set(v___x_1252_, 1, v___x_1250_);
    return v___x_1252_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    v___x_1253_ = lean_unsigned_to_nat(32);
    v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
    v___x_1255_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1255_, 0, v___x_1254_);
    return v___x_1255_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1256_ = 5usize;
    v___x_1257_ = lean_unsigned_to_nat(0);
    v___x_1258_ = lean_unsigned_to_nat(32);
    v___x_1259_ = lean_mk_empty_array_with_capacity(v___x_1258_);
    v___x_1260_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3,
    );
    v___x_1261_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    lean_ctor_set(v___x_1261_, 1, v___x_1259_);
    lean_ctor_set(v___x_1261_, 2, v___x_1257_);
    lean_ctor_set(v___x_1261_, 3, v___x_1257_);
    lean_ctor_set_usize(v___x_1261_, 4, v___x_1256_);
    return v___x_1261_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4,
    );
    v___x_1263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    v___x_1264_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    lean_ctor_set(v___x_1264_, 2, v___x_1263_);
    lean_ctor_set(v___x_1264_, 3, v___x_1262_);
    return v___x_1264_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5,
    );
    v___x_1266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2,
    );
    v___x_1267_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1267_, 0, v___x_1266_);
    lean_ctor_set(v___x_1267_, 1, v___x_1265_);
    return v___x_1267_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(
    mut v_a_1268_: *mut LeanObject,
    mut v_ctx_1269_: *mut LeanObject,
    mut v_simprocs_1270_: *mut LeanObject,
    mut v_d_x3f_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
    );
    v___x_1282_ = l_Lean_Meta_simp(
        v_a_1268_,
        v_ctx_1269_,
        v_simprocs_1270_,
        v_d_x3f_1271_,
        v___x_1281_,
        v___y_1276_,
        v___y_1277_,
        v___y_1278_,
        v___y_1279_,
    );
    return v___x_1282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(
    mut v_a_1283_: *mut LeanObject,
    mut v_ctx_1284_: *mut LeanObject,
    mut v_simprocs_1285_: *mut LeanObject,
    mut v_d_x3f_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1296_: *mut LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(
        v_a_1283_,
        v_ctx_1284_,
        v_simprocs_1285_,
        v_d_x3f_1286_,
        v___y_1287_,
        v___y_1288_,
        v___y_1289_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
    );
    lean_dec(v___y_1294_);
    lean_dec_ref(v___y_1293_);
    lean_dec(v___y_1292_);
    lean_dec_ref(v___y_1291_);
    lean_dec(v___y_1290_);
    lean_dec_ref(v___y_1289_);
    lean_dec(v___y_1288_);
    lean_dec_ref(v___y_1287_);
    return v_res_1296_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(
    mut v_stx_1297_: *mut LeanObject,
    mut v___x_1298_: u8,
    mut v___x_1299_: u8,
    mut v___x_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_a_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_a_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v_stx_1297_,
                    v___x_1298_,
                    v___x_1299_,
                    v___x_1298_,
                    v___x_1300_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1305_,
                    v___y_1306_,
                    v___y_1307_,
                    v___y_1308_,
                );
                if lean_obj_tag(v___x_1310_) == 0 {
                    v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
                    lean_inc(v_a_1311_);
                    lean_dec_ref_known(v___x_1310_, 1);
                    v_ctx_1312_ = lean_ctor_get(v_a_1311_, 0);
                    lean_inc_ref(v_ctx_1312_);
                    v_simprocs_1313_ = lean_ctor_get(v_a_1311_, 1);
                    lean_inc_ref(v_simprocs_1313_);
                    v_dischargeWrapper_1314_ = lean_ctor_get(v_a_1311_, 2);
                    lean_inc(v_dischargeWrapper_1314_);
                    lean_dec(v_a_1311_);
                    v___x_1315_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_1302_,
                        v___y_1305_,
                        v___y_1306_,
                        v___y_1307_,
                        v___y_1308_,
                    );
                    if lean_obj_tag(v___x_1315_) == 0 {
                        v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
                        lean_inc(v_a_1316_);
                        lean_dec_ref_known(v___x_1315_, 1);
                        v___f_1317_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed
                                as *mut core::ffi::c_void,
                            13,
                            3,
                        );
                        lean_closure_set(v___f_1317_, 0, v_a_1316_);
                        lean_closure_set(v___f_1317_, 1, v_ctx_1312_);
                        lean_closure_set(v___f_1317_, 2, v_simprocs_1313_);
                        v___x_1318_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                            v_dischargeWrapper_1314_,
                            v___f_1317_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                            v___y_1307_,
                            v___y_1308_,
                        );
                        lean_dec(v_dischargeWrapper_1314_);
                        if lean_obj_tag(v___x_1318_) == 0 {
                            v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
                            lean_inc(v_a_1319_);
                            lean_dec_ref_known(v___x_1318_, 1);
                            v_fst_1320_ = lean_ctor_get(v_a_1319_, 0);
                            lean_inc(v_fst_1320_);
                            lean_dec(v_a_1319_);
                            v___x_1321_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                                v_fst_1320_,
                                v___y_1301_,
                                v___y_1302_,
                                v___y_1303_,
                                v___y_1304_,
                                v___y_1305_,
                                v___y_1306_,
                                v___y_1307_,
                                v___y_1308_,
                            );
                            return v___x_1321_;
                        } else {
                            v_a_1322_ = lean_ctor_get(v___x_1318_, 0);
                            v_isSharedCheck_1329_ = (!lean_is_exclusive(v___x_1318_)) as u8;
                            if v_isSharedCheck_1329_ == 0 {
                                v___x_1324_ = v___x_1318_;
                                v_isShared_1325_ = v_isSharedCheck_1329_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1322_);
                                lean_dec(v___x_1318_);
                                v___x_1324_ = lean_box(0);
                                v_isShared_1325_ = v_isSharedCheck_1329_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_dischargeWrapper_1314_);
                        lean_dec_ref(v_simprocs_1313_);
                        lean_dec_ref(v_ctx_1312_);
                        v_a_1330_ = lean_ctor_get(v___x_1315_, 0);
                        v_isSharedCheck_1337_ = (!lean_is_exclusive(v___x_1315_)) as u8;
                        if v_isSharedCheck_1337_ == 0 {
                            v___x_1332_ = v___x_1315_;
                            v_isShared_1333_ = v_isSharedCheck_1337_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1330_);
                            lean_dec(v___x_1315_);
                            v___x_1332_ = lean_box(0);
                            v_isShared_1333_ = v_isSharedCheck_1337_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1338_ = lean_ctor_get(v___x_1310_, 0);
                    v_isSharedCheck_1345_ = (!lean_is_exclusive(v___x_1310_)) as u8;
                    if v_isSharedCheck_1345_ == 0 {
                        v___x_1340_ = v___x_1310_;
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1338_);
                        lean_dec(v___x_1310_);
                        v___x_1340_ = lean_box(0);
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1325_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
                    v___x_1327_ = v_reuseFailAlloc_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1327_;
            }
            3 => {
                if v_isShared_1333_ == 0 {
                    v___x_1335_ = v___x_1332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1335_;
            }
            5 => {
                if v_isShared_1341_ == 0 {
                    v___x_1343_ = v___x_1340_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(
    mut v_stx_1346_: *mut LeanObject,
    mut v___x_1347_: *mut LeanObject,
    mut v___x_1348_: *mut LeanObject,
    mut v___x_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
    mut v___y_1351_: *mut LeanObject,
    mut v___y_1352_: *mut LeanObject,
    mut v___y_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
    mut v___y_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
    mut v___y_1358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_754__boxed_1359_: u8 = 0;
    let mut v___x_755__boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_754__boxed_1359_ = (lean_unbox(v___x_1347_) as u8);
    v___x_755__boxed_1360_ = (lean_unbox(v___x_1348_) as u8);
    v_res_1361_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(
        v_stx_1346_,
        v___x_754__boxed_1359_,
        v___x_755__boxed_1360_,
        v___x_1349_,
        v___y_1350_,
        v___y_1351_,
        v___y_1352_,
        v___y_1353_,
        v___y_1354_,
        v___y_1355_,
        v___y_1356_,
        v___y_1357_,
    );
    lean_dec(v___y_1357_);
    lean_dec_ref(v___y_1356_);
    lean_dec(v___y_1355_);
    lean_dec_ref(v___y_1354_);
    lean_dec(v___y_1353_);
    lean_dec_ref(v___y_1352_);
    lean_dec(v___y_1351_);
    lean_dec_ref(v___y_1350_);
    lean_dec(v_stx_1346_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp(
    mut v_stx_1363_: *mut LeanObject,
    mut v_a_1364_: *mut LeanObject,
    mut v_a_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
    mut v_a_1368_: *mut LeanObject,
    mut v_a_1369_: *mut LeanObject,
    mut v_a_1370_: *mut LeanObject,
    mut v_a_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1373_ = 0;
    v___x_1374_ = 0;
    v___x_1375_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
    v___x_1376_ = lean_box((v___x_1373_) as usize);
    v___x_1377_ = lean_box((v___x_1374_) as usize);
    v___f_1378_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_1378_, 0, v_stx_1363_);
    lean_closure_set(v___f_1378_, 1, v___x_1376_);
    lean_closure_set(v___f_1378_, 2, v___x_1377_);
    lean_closure_set(v___f_1378_, 3, v___x_1375_);
    v___x_1379_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1378_,
        v_a_1364_,
        v_a_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
        v_a_1370_,
        v_a_1371_,
    );
    return v___x_1379_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___boxed(
    mut v_stx_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1390_: *mut LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Lean_Elab_Tactic_Conv_evalSimp(
        v_stx_1380_,
        v_a_1381_,
        v_a_1382_,
        v_a_1383_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
    );
    lean_dec(v_a_1388_);
    lean_dec_ref(v_a_1387_);
    lean_dec(v_a_1386_);
    lean_dec_ref(v_a_1385_);
    lean_dec(v_a_1384_);
    lean_dec_ref(v_a_1383_);
    lean_dec(v_a_1382_);
    lean_dec_ref(v_a_1381_);
    return v_res_1390_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1()
-> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1412_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5;
    v___x_1413_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8;
    v___x_1414_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1415_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1411_,
        v___x_1412_,
        v___x_1413_,
        v___x_1414_,
    );
    return v___x_1415_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(
    mut v_a_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1417_: *mut LeanObject = core::ptr::null_mut();
    v_res_1417_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
    return v_res_1417_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3()
-> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8;
    v___x_1444_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6;
    v___x_1445_ = l_Lean_addBuiltinDeclarationRanges(v___x_1443_, v___x_1444_);
    return v___x_1445_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(
    mut v_a_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1447_: *mut LeanObject = core::ptr::null_mut();
    v_res_1447_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
    return v_res_1447_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_box(0);
    v___x_1449_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1450_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    lean_ctor_set(v___x_1450_, 1, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
    v___x_1453_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1453_, 0, v___x_1452_);
    return v___x_1453_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
    return v_res_1455_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(
    mut v_00_u03b1_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    v___x_1466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
    return v___x_1466_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(
    mut v_00_u03b1_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
    mut v___y_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(
            v_00_u03b1_1467_,
            v___y_1468_,
            v___y_1469_,
            v___y_1470_,
            v___y_1471_,
            v___y_1472_,
            v___y_1473_,
            v___y_1474_,
            v___y_1475_,
        );
    lean_dec(v___y_1475_);
    lean_dec_ref(v___y_1474_);
    lean_dec(v___y_1473_);
    lean_dec_ref(v___y_1472_);
    lean_dec(v___y_1471_);
    lean_dec_ref(v___y_1470_);
    lean_dec(v___y_1469_);
    lean_dec_ref(v___y_1468_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(
    mut v___x_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
    mut v_ctx_1480_: *mut LeanObject,
    mut v_simprocs_1481_: *mut LeanObject,
    mut v_d_x3f_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    lean_inc_n(v___x_1478_, 2);
    v___x_1493_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1493_, 0, v___x_1492_);
    lean_ctor_set(v___x_1493_, 1, v___x_1478_);
    v___x_1494_ = lean_unsigned_to_nat(32);
    v___x_1495_ = lean_mk_empty_array_with_capacity(v___x_1494_);
    v___x_1496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3,
    );
    v___x_1497_ = 5usize;
    v___x_1498_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1498_, 0, v___x_1496_);
    lean_ctor_set(v___x_1498_, 1, v___x_1495_);
    lean_ctor_set(v___x_1498_, 2, v___x_1478_);
    lean_ctor_set(v___x_1498_, 3, v___x_1478_);
    lean_ctor_set_usize(v___x_1498_, 4, v___x_1497_);
    v___x_1499_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1499_, 0, v___x_1492_);
    lean_ctor_set(v___x_1499_, 1, v___x_1492_);
    lean_ctor_set(v___x_1499_, 2, v___x_1492_);
    lean_ctor_set(v___x_1499_, 3, v___x_1498_);
    v___x_1500_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1500_, 0, v___x_1493_);
    lean_ctor_set(v___x_1500_, 1, v___x_1499_);
    v___x_1501_ = l_Lean_Meta_simp(
        v_a_1479_,
        v_ctx_1480_,
        v_simprocs_1481_,
        v_d_x3f_1482_,
        v___x_1500_,
        v___y_1487_,
        v___y_1488_,
        v___y_1489_,
        v___y_1490_,
    );
    lean_dec_ref_known(v___x_1500_, 2);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(
    mut v___x_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_ctx_1504_: *mut LeanObject,
    mut v_simprocs_1505_: *mut LeanObject,
    mut v_d_x3f_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1516_: *mut LeanObject = core::ptr::null_mut();
    v_res_1516_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(
        v___x_1502_,
        v_a_1503_,
        v_ctx_1504_,
        v_simprocs_1505_,
        v_d_x3f_1506_,
        v___y_1507_,
        v___y_1508_,
        v___y_1509_,
        v___y_1510_,
        v___y_1511_,
        v___y_1512_,
        v___y_1513_,
        v___y_1514_,
    );
    lean_dec(v___y_1514_);
    lean_dec_ref(v___y_1513_);
    lean_dec(v___y_1512_);
    lean_dec_ref(v___y_1511_);
    lean_dec(v___y_1510_);
    lean_dec_ref(v___y_1509_);
    lean_dec(v___y_1508_);
    lean_dec_ref(v___y_1507_);
    return v_res_1516_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10() -> *mut LeanObject
{
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Array_mkArray0(lean_box(0));
    return v___x_1530_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(
    mut v___x_1532_: u8,
    mut v_stx_1533_: *mut LeanObject,
    mut v___x_1534_: *mut LeanObject,
    mut v___x_1535_: *mut LeanObject,
    mut v___x_1536_: *mut LeanObject,
    mut v___x_1537_: u8,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
    mut v___y_1542_: *mut LeanObject,
    mut v___y_1543_: *mut LeanObject,
    mut v___y_1544_: *mut LeanObject,
    mut v___y_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: u8 = 0;
    let mut v___y_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v_usedTheorems_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_unused_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v___y_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: u8 = 0;
    let mut v___y_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: u8 = 0;
    let mut v___y_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_o_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1532_ == 0 {
                    lean_dec_ref(v___x_1536_);
                    lean_dec_ref(v___x_1535_);
                    lean_dec_ref(v___x_1534_);
                    v___x_1547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                    return v___x_1547_;
                } else {
                    v___x_1548_ = lean_unsigned_to_nat(1);
                    v___x_1549_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1548_);
                    v___x_1550_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0;
                    lean_inc_ref(v___x_1536_);
                    lean_inc_ref(v___x_1535_);
                    lean_inc_ref(v___x_1534_);
                    v___x_1551_ =
                        l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1550_);
                    lean_inc(v___x_1549_);
                    v___x_1552_ = l_Lean_Syntax_isOfKind(v___x_1549_, v___x_1551_);
                    lean_dec(v___x_1551_);
                    if v___x_1552_ == 0 {
                        lean_dec(v___x_1549_);
                        lean_dec_ref(v___x_1536_);
                        lean_dec_ref(v___x_1535_);
                        lean_dec_ref(v___x_1534_);
                        v___x_1553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_1553_;
                    } else {
                        v___x_1554_ = lean_unsigned_to_nat(0);
                        v_tk_1555_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1554_);
                        v___x_1733_ = lean_unsigned_to_nat(2);
                        v___x_1734_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1733_);
                        v___x_1780_ = lean_unsigned_to_nat(3);
                        v___x_1781_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1780_);
                        v___x_1782_ = l_Lean_Syntax_isNone(v___x_1781_);
                        if v___x_1782_ == 0 {
                            lean_inc(v___x_1781_);
                            v___x_1783_ = l_Lean_Syntax_matchesNull(v___x_1781_, v___x_1548_);
                            if v___x_1783_ == 0 {
                                lean_dec(v___x_1781_);
                                lean_dec(v___x_1734_);
                                lean_dec(v_tk_1555_);
                                lean_dec(v___x_1549_);
                                lean_dec_ref(v___x_1536_);
                                lean_dec_ref(v___x_1535_);
                                lean_dec_ref(v___x_1534_);
                                v___x_1784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                                return v___x_1784_;
                            } else {
                                v_o_1785_ = l_Lean_Syntax_getArg(v___x_1781_, v___x_1554_);
                                lean_dec(v___x_1781_);
                                v___x_1786_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1786_, 0, v_o_1785_);
                                v_o_1757_ = v___x_1786_;
                                v___y_1758_ = v___y_1538_;
                                v___y_1759_ = v___y_1539_;
                                v___y_1760_ = v___y_1540_;
                                v___y_1761_ = v___y_1541_;
                                v___y_1762_ = v___y_1542_;
                                v___y_1763_ = v___y_1543_;
                                v___y_1764_ = v___y_1544_;
                                v___y_1765_ = v___y_1545_;
                                state = 20;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1781_);
                            v___x_1787_ = lean_box(0);
                            v_o_1757_ = v___x_1787_;
                            v___y_1758_ = v___y_1538_;
                            v___y_1759_ = v___y_1539_;
                            v___y_1760_ = v___y_1540_;
                            v___y_1761_ = v___y_1541_;
                            v___y_1762_ = v___y_1542_;
                            v___y_1763_ = v___y_1543_;
                            v___y_1764_ = v___y_1544_;
                            v___y_1765_ = v___y_1545_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_1557_, 2);
                v___x_1575_ = l_Array_append___redArg(v___y_1557_, v___y_1574_);
                lean_dec_ref(v___y_1574_);
                lean_inc_n(v___y_1564_, 2);
                lean_inc_n(v___y_1563_, 2);
                v___x_1576_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1576_, 0, v___y_1563_);
                lean_ctor_set(v___x_1576_, 1, v___y_1564_);
                lean_ctor_set(v___x_1576_, 2, v___x_1575_);
                v___x_1577_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1577_, 0, v___y_1563_);
                lean_ctor_set(v___x_1577_, 1, v___y_1564_);
                lean_ctor_set(v___x_1577_, 2, v___y_1557_);
                v___x_1578_ = l_Lean_Syntax_node6(
                    v___y_1563_,
                    v___y_1561_,
                    v___y_1570_,
                    v___x_1549_,
                    v___y_1569_,
                    v___y_1560_,
                    v___x_1576_,
                    v___x_1577_,
                );
                v___x_1579_ = 0;
                v___x_1580_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
                v___x_1581_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___x_1578_,
                    v___y_1565_,
                    v___x_1579_,
                    v___y_1565_,
                    v___x_1580_,
                    v___y_1558_,
                    v___y_1567_,
                    v___y_1566_,
                    v___y_1562_,
                    v___y_1573_,
                    v___y_1568_,
                    v___y_1571_,
                    v___y_1559_,
                );
                if lean_obj_tag(v___x_1581_) == 0 {
                    v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
                    lean_inc(v_a_1582_);
                    lean_dec_ref_known(v___x_1581_, 1);
                    v_ctx_1583_ = lean_ctor_get(v_a_1582_, 0);
                    lean_inc_ref(v_ctx_1583_);
                    v_simprocs_1584_ = lean_ctor_get(v_a_1582_, 1);
                    lean_inc_ref(v_simprocs_1584_);
                    v_dischargeWrapper_1585_ = lean_ctor_get(v_a_1582_, 2);
                    lean_inc(v_dischargeWrapper_1585_);
                    lean_dec(v_a_1582_);
                    v___x_1586_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_1567_,
                        v___y_1573_,
                        v___y_1568_,
                        v___y_1571_,
                        v___y_1559_,
                    );
                    if lean_obj_tag(v___x_1586_) == 0 {
                        v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
                        lean_inc(v_a_1587_);
                        lean_dec_ref_known(v___x_1586_, 1);
                        v___f_1588_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed
                                as *mut core::ffi::c_void,
                            14,
                            4,
                        );
                        lean_closure_set(v___f_1588_, 0, v___x_1554_);
                        lean_closure_set(v___f_1588_, 1, v_a_1587_);
                        lean_closure_set(v___f_1588_, 2, v_ctx_1583_);
                        lean_closure_set(v___f_1588_, 3, v_simprocs_1584_);
                        v___x_1589_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                            v_dischargeWrapper_1585_,
                            v___f_1588_,
                            v___y_1558_,
                            v___y_1567_,
                            v___y_1566_,
                            v___y_1562_,
                            v___y_1573_,
                            v___y_1568_,
                            v___y_1571_,
                            v___y_1559_,
                        );
                        lean_dec(v_dischargeWrapper_1585_);
                        if lean_obj_tag(v___x_1589_) == 0 {
                            v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
                            lean_inc(v_a_1590_);
                            lean_dec_ref_known(v___x_1589_, 1);
                            v_fst_1591_ = lean_ctor_get(v_a_1590_, 0);
                            lean_inc(v_fst_1591_);
                            v_snd_1592_ = lean_ctor_get(v_a_1590_, 1);
                            lean_inc(v_snd_1592_);
                            lean_dec(v_a_1590_);
                            v___x_1593_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                                v_fst_1591_,
                                v___y_1558_,
                                v___y_1567_,
                                v___y_1566_,
                                v___y_1562_,
                                v___y_1573_,
                                v___y_1568_,
                                v___y_1571_,
                                v___y_1559_,
                            );
                            if lean_obj_tag(v___x_1593_) == 0 {
                                v_isSharedCheck_1626_ = (!lean_is_exclusive(v___x_1593_)) as u8;
                                if v_isSharedCheck_1626_ == 0 {
                                    v_unused_1627_ = lean_ctor_get(v___x_1593_, 0);
                                    lean_dec(v_unused_1627_);
                                    v___x_1595_ = v___x_1593_;
                                    v_isShared_1596_ = v_isSharedCheck_1626_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v___x_1593_);
                                    v___x_1595_ = lean_box(0);
                                    v_isShared_1596_ = v_isSharedCheck_1626_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_1592_);
                                lean_dec(v___x_1578_);
                                lean_dec(v_tk_1555_);
                                return v___x_1593_;
                            }
                        } else {
                            lean_dec(v___x_1578_);
                            lean_dec(v_tk_1555_);
                            v_a_1628_ = lean_ctor_get(v___x_1589_, 0);
                            v_isSharedCheck_1635_ = (!lean_is_exclusive(v___x_1589_)) as u8;
                            if v_isSharedCheck_1635_ == 0 {
                                v___x_1630_ = v___x_1589_;
                                v_isShared_1631_ = v_isSharedCheck_1635_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1628_);
                                lean_dec(v___x_1589_);
                                v___x_1630_ = lean_box(0);
                                v_isShared_1631_ = v_isSharedCheck_1635_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_dischargeWrapper_1585_);
                        lean_dec_ref(v_simprocs_1584_);
                        lean_dec_ref(v_ctx_1583_);
                        lean_dec(v___x_1578_);
                        lean_dec(v_tk_1555_);
                        v_a_1636_ = lean_ctor_get(v___x_1586_, 0);
                        v_isSharedCheck_1643_ = (!lean_is_exclusive(v___x_1586_)) as u8;
                        if v_isSharedCheck_1643_ == 0 {
                            v___x_1638_ = v___x_1586_;
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1636_);
                            lean_dec(v___x_1586_);
                            v___x_1638_ = lean_box(0);
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1578_);
                    lean_dec(v_tk_1555_);
                    v_a_1644_ = lean_ctor_get(v___x_1581_, 0);
                    v_isSharedCheck_1651_ = (!lean_is_exclusive(v___x_1581_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v___x_1646_ = v___x_1581_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1644_);
                        lean_dec(v___x_1581_);
                        v___x_1646_ = lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_usedTheorems_1597_ = lean_ctor_get(v_snd_1592_, 0);
                v_isSharedCheck_1624_ = (!lean_is_exclusive(v_snd_1592_)) as u8;
                if v_isSharedCheck_1624_ == 0 {
                    v_unused_1625_ = lean_ctor_get(v_snd_1592_, 1);
                    lean_dec(v_unused_1625_);
                    v___x_1599_ = v_snd_1592_;
                    v_isShared_1600_ = v_isSharedCheck_1624_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_usedTheorems_1597_);
                    lean_dec(v_snd_1592_);
                    v___x_1599_ = lean_box(0);
                    v_isShared_1600_ = v_isSharedCheck_1624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1601_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___x_1578_,
                    v_usedTheorems_1597_,
                    v___y_1573_,
                    v___y_1568_,
                    v___y_1571_,
                    v___y_1559_,
                );
                lean_dec_ref(v_usedTheorems_1597_);
                if lean_obj_tag(v___x_1601_) == 0 {
                    v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
                    lean_inc(v_a_1602_);
                    lean_dec_ref_known(v___x_1601_, 1);
                    v___x_1603_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2;
                    if v_isShared_1600_ == 0 {
                        lean_ctor_set(v___x_1599_, 1, v_a_1602_);
                        lean_ctor_set(v___x_1599_, 0, v___x_1603_);
                        v___x_1605_ = v___x_1599_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1603_);
                        lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_a_1602_);
                        v___x_1605_ = v_reuseFailAlloc_1615_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1599_);
                    lean_del_object(v___x_1595_);
                    lean_dec(v_tk_1555_);
                    v_a_1616_ = lean_ctor_get(v___x_1601_, 0);
                    v_isSharedCheck_1623_ = (!lean_is_exclusive(v___x_1601_)) as u8;
                    if v_isSharedCheck_1623_ == 0 {
                        v___x_1618_ = v___x_1601_;
                        v_isShared_1619_ = v_isSharedCheck_1623_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1616_);
                        lean_dec(v___x_1601_);
                        v___x_1618_ = lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1623_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1606_ = lean_box(0);
                v___x_1607_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_1607_, 0, v___x_1605_);
                lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                lean_ctor_set(v___x_1607_, 2, v___x_1606_);
                lean_ctor_set(v___x_1607_, 3, v___x_1606_);
                lean_ctor_set(v___x_1607_, 4, v___x_1606_);
                lean_ctor_set(v___x_1607_, 5, v___x_1606_);
                lean_inc(v___y_1572_);
                if v_isShared_1596_ == 0 {
                    lean_ctor_set_tag(v___x_1595_, 1);
                    lean_ctor_set(v___x_1595_, 0, v___y_1572_);
                    v___x_1609_ = v___x_1595_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___y_1572_);
                    v___x_1609_ = v_reuseFailAlloc_1614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1610_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3;
                v___x_1611_ = 4;
                v___x_1612_ = l_Lean_MessageData_nil;
                v___x_1613_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_1555_,
                    v___x_1607_,
                    v___x_1609_,
                    v___x_1610_,
                    v___x_1606_,
                    v___x_1611_,
                    v___x_1612_,
                    v___y_1571_,
                    v___y_1559_,
                );
                return v___x_1613_;
            }
            6 => {
                if v_isShared_1619_ == 0 {
                    v___x_1621_ = v___x_1618_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1621_;
            }
            8 => {
                if v_isShared_1631_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1633_;
            }
            10 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1641_;
            }
            12 => {
                if v_isShared_1647_ == 0 {
                    v___x_1649_ = v___x_1646_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1649_;
            }
            14 => {
                lean_inc_ref(v___y_1653_);
                v___x_1671_ = l_Array_append___redArg(v___y_1653_, v___y_1670_);
                lean_dec_ref(v___y_1670_);
                lean_inc(v___y_1659_);
                lean_inc(v___y_1658_);
                v___x_1672_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1672_, 0, v___y_1658_);
                lean_ctor_set(v___x_1672_, 1, v___y_1659_);
                lean_ctor_set(v___x_1672_, 2, v___x_1671_);
                if lean_obj_tag(v___y_1662_) == 1 {
                    v_val_1673_ = lean_ctor_get(v___y_1662_, 0);
                    lean_inc(v_val_1673_);
                    lean_dec_ref_known(v___y_1662_, 1);
                    v___x_1674_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4;
                    lean_inc_n(v___y_1658_, 3);
                    v___x_1675_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1675_, 0, v___y_1658_);
                    lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                    lean_inc_ref(v___y_1653_);
                    v___x_1676_ = l_Array_append___redArg(v___y_1653_, v_val_1673_);
                    lean_dec(v_val_1673_);
                    lean_inc(v___y_1659_);
                    v___x_1677_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1677_, 0, v___y_1658_);
                    lean_ctor_set(v___x_1677_, 1, v___y_1659_);
                    lean_ctor_set(v___x_1677_, 2, v___x_1676_);
                    v___x_1678_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5;
                    v___x_1679_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1679_, 0, v___y_1658_);
                    lean_ctor_set(v___x_1679_, 1, v___x_1678_);
                    v___x_1680_ = l_Array_mkArray3___redArg(v___x_1675_, v___x_1677_, v___x_1679_);
                    v___y_1557_ = v___y_1653_;
                    v___y_1558_ = v___y_1654_;
                    v___y_1559_ = v___y_1655_;
                    v___y_1560_ = v___x_1672_;
                    v___y_1561_ = v___y_1656_;
                    v___y_1562_ = v___y_1657_;
                    v___y_1563_ = v___y_1658_;
                    v___y_1564_ = v___y_1659_;
                    v___y_1565_ = v___y_1660_;
                    v___y_1566_ = v___y_1661_;
                    v___y_1567_ = v___y_1663_;
                    v___y_1568_ = v___y_1664_;
                    v___y_1569_ = v___y_1665_;
                    v___y_1570_ = v___y_1666_;
                    v___y_1571_ = v___y_1667_;
                    v___y_1572_ = v___y_1669_;
                    v___y_1573_ = v___y_1668_;
                    v___y_1574_ = v___x_1680_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1662_);
                    v___x_1681_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1557_ = v___y_1653_;
                    v___y_1558_ = v___y_1654_;
                    v___y_1559_ = v___y_1655_;
                    v___y_1560_ = v___x_1672_;
                    v___y_1561_ = v___y_1656_;
                    v___y_1562_ = v___y_1657_;
                    v___y_1563_ = v___y_1658_;
                    v___y_1564_ = v___y_1659_;
                    v___y_1565_ = v___y_1660_;
                    v___y_1566_ = v___y_1661_;
                    v___y_1567_ = v___y_1663_;
                    v___y_1568_ = v___y_1664_;
                    v___y_1569_ = v___y_1665_;
                    v___y_1570_ = v___y_1666_;
                    v___y_1571_ = v___y_1667_;
                    v___y_1572_ = v___y_1669_;
                    v___y_1573_ = v___y_1668_;
                    v___y_1574_ = v___x_1681_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                lean_inc_ref(v___y_1683_);
                v___x_1701_ = l_Array_append___redArg(v___y_1683_, v___y_1700_);
                lean_dec_ref(v___y_1700_);
                lean_inc(v___y_1689_);
                lean_inc(v___y_1688_);
                v___x_1702_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1702_, 0, v___y_1688_);
                lean_ctor_set(v___x_1702_, 1, v___y_1689_);
                lean_ctor_set(v___x_1702_, 2, v___x_1701_);
                if lean_obj_tag(v___y_1694_) == 1 {
                    v_val_1703_ = lean_ctor_get(v___y_1694_, 0);
                    lean_inc(v_val_1703_);
                    lean_dec_ref_known(v___y_1694_, 1);
                    v___x_1704_ = l_Lean_SourceInfo_fromRef(v_val_1703_, v___x_1537_);
                    lean_dec(v_val_1703_);
                    v___x_1705_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7;
                    v___x_1706_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1706_, 0, v___x_1704_);
                    lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                    v___x_1707_ = l_Array_mkArray1___redArg(v___x_1706_);
                    v___y_1653_ = v___y_1683_;
                    v___y_1654_ = v___y_1684_;
                    v___y_1655_ = v___y_1685_;
                    v___y_1656_ = v___y_1686_;
                    v___y_1657_ = v___y_1687_;
                    v___y_1658_ = v___y_1688_;
                    v___y_1659_ = v___y_1689_;
                    v___y_1660_ = v___y_1690_;
                    v___y_1661_ = v___y_1691_;
                    v___y_1662_ = v___y_1692_;
                    v___y_1663_ = v___y_1693_;
                    v___y_1664_ = v___y_1695_;
                    v___y_1665_ = v___x_1702_;
                    v___y_1666_ = v___y_1696_;
                    v___y_1667_ = v___y_1697_;
                    v___y_1668_ = v___y_1699_;
                    v___y_1669_ = v___y_1698_;
                    v___y_1670_ = v___x_1707_;
                    state = 14;
                    continue;
                } else {
                    lean_dec(v___y_1694_);
                    v___x_1708_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1653_ = v___y_1683_;
                    v___y_1654_ = v___y_1684_;
                    v___y_1655_ = v___y_1685_;
                    v___y_1656_ = v___y_1686_;
                    v___y_1657_ = v___y_1687_;
                    v___y_1658_ = v___y_1688_;
                    v___y_1659_ = v___y_1689_;
                    v___y_1660_ = v___y_1690_;
                    v___y_1661_ = v___y_1691_;
                    v___y_1662_ = v___y_1692_;
                    v___y_1663_ = v___y_1693_;
                    v___y_1664_ = v___y_1695_;
                    v___y_1665_ = v___x_1702_;
                    v___y_1666_ = v___y_1696_;
                    v___y_1667_ = v___y_1697_;
                    v___y_1668_ = v___y_1699_;
                    v___y_1669_ = v___y_1698_;
                    v___y_1670_ = v___x_1708_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v_ref_1721_ = lean_ctor_get(v___y_1718_, 5);
                v___x_1722_ = 0;
                v___x_1723_ = l_Lean_SourceInfo_fromRef(v_ref_1721_, v___x_1722_);
                v___x_1724_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4;
                v___x_1725_ =
                    l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1724_);
                v___x_1726_ = l_Lean_SourceInfo_fromRef(v_tk_1555_, v___x_1537_);
                v___x_1727_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1727_, 0, v___x_1726_);
                lean_ctor_set(v___x_1727_, 1, v___x_1724_);
                v___x_1728_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9;
                v___x_1729_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10,
                );
                if lean_obj_tag(v___y_1720_) == 1 {
                    v_val_1730_ = lean_ctor_get(v___y_1720_, 0);
                    lean_inc(v_val_1730_);
                    lean_dec_ref_known(v___y_1720_, 1);
                    v___x_1731_ = l_Array_mkArray1___redArg(v_val_1730_);
                    v___y_1683_ = v___x_1729_;
                    v___y_1684_ = v___y_1712_;
                    v___y_1685_ = v___y_1714_;
                    v___y_1686_ = v___x_1725_;
                    v___y_1687_ = v___y_1717_;
                    v___y_1688_ = v___x_1723_;
                    v___y_1689_ = v___x_1728_;
                    v___y_1690_ = v___x_1722_;
                    v___y_1691_ = v___y_1710_;
                    v___y_1692_ = v___y_1711_;
                    v___y_1693_ = v___y_1713_;
                    v___y_1694_ = v___y_1716_;
                    v___y_1695_ = v___y_1715_;
                    v___y_1696_ = v___x_1727_;
                    v___y_1697_ = v___y_1718_;
                    v___y_1698_ = v_ref_1721_;
                    v___y_1699_ = v___y_1719_;
                    v___y_1700_ = v___x_1731_;
                    state = 15;
                    continue;
                } else {
                    lean_dec(v___y_1720_);
                    v___x_1732_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1683_ = v___x_1729_;
                    v___y_1684_ = v___y_1712_;
                    v___y_1685_ = v___y_1714_;
                    v___y_1686_ = v___x_1725_;
                    v___y_1687_ = v___y_1717_;
                    v___y_1688_ = v___x_1723_;
                    v___y_1689_ = v___x_1728_;
                    v___y_1690_ = v___x_1722_;
                    v___y_1691_ = v___y_1710_;
                    v___y_1692_ = v___y_1711_;
                    v___y_1693_ = v___y_1713_;
                    v___y_1694_ = v___y_1716_;
                    v___y_1695_ = v___y_1715_;
                    v___y_1696_ = v___x_1727_;
                    v___y_1697_ = v___y_1718_;
                    v___y_1698_ = v_ref_1721_;
                    v___y_1699_ = v___y_1719_;
                    v___y_1700_ = v___x_1732_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_1746_ = l_Lean_Syntax_getOptional_x3f(v___x_1734_);
                lean_dec(v___x_1734_);
                if lean_obj_tag(v___x_1746_) == 0 {
                    v___x_1747_ = lean_box(0);
                    v___y_1710_ = v___y_1740_;
                    v___y_1711_ = v_args_1737_;
                    v___y_1712_ = v___y_1738_;
                    v___y_1713_ = v___y_1739_;
                    v___y_1714_ = v___y_1745_;
                    v___y_1715_ = v___y_1743_;
                    v___y_1716_ = v___y_1736_;
                    v___y_1717_ = v___y_1741_;
                    v___y_1718_ = v___y_1744_;
                    v___y_1719_ = v___y_1742_;
                    v___y_1720_ = v___x_1747_;
                    state = 16;
                    continue;
                } else {
                    v_val_1748_ = lean_ctor_get(v___x_1746_, 0);
                    v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1746_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_val_1748_);
                        lean_dec(v___x_1746_);
                        v___x_1750_ = lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_val_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_1710_ = v___y_1740_;
                v___y_1711_ = v_args_1737_;
                v___y_1712_ = v___y_1738_;
                v___y_1713_ = v___y_1739_;
                v___y_1714_ = v___y_1745_;
                v___y_1715_ = v___y_1743_;
                v___y_1716_ = v___y_1736_;
                v___y_1717_ = v___y_1741_;
                v___y_1718_ = v___y_1744_;
                v___y_1719_ = v___y_1742_;
                v___y_1720_ = v___x_1753_;
                state = 16;
                continue;
            }
            20 => {
                v___x_1766_ = lean_unsigned_to_nat(4);
                v___x_1767_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1766_);
                v___x_1768_ = l_Lean_Syntax_isNone(v___x_1767_);
                if v___x_1768_ == 0 {
                    lean_inc(v___x_1767_);
                    v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1548_);
                    if v___x_1769_ == 0 {
                        lean_dec(v___x_1767_);
                        lean_dec(v_o_1757_);
                        lean_dec(v___x_1734_);
                        lean_dec(v_tk_1555_);
                        lean_dec(v___x_1549_);
                        lean_dec_ref(v___x_1536_);
                        lean_dec_ref(v___x_1535_);
                        lean_dec_ref(v___x_1534_);
                        v___x_1770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_1770_;
                    } else {
                        v___x_1771_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1554_);
                        lean_dec(v___x_1767_);
                        v___x_1772_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11;
                        lean_inc_ref(v___x_1536_);
                        lean_inc_ref(v___x_1535_);
                        lean_inc_ref(v___x_1534_);
                        v___x_1773_ =
                            l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1772_);
                        lean_inc(v___x_1771_);
                        v___x_1774_ = l_Lean_Syntax_isOfKind(v___x_1771_, v___x_1773_);
                        lean_dec(v___x_1773_);
                        if v___x_1774_ == 0 {
                            lean_dec(v___x_1771_);
                            lean_dec(v_o_1757_);
                            lean_dec(v___x_1734_);
                            lean_dec(v_tk_1555_);
                            lean_dec(v___x_1549_);
                            lean_dec_ref(v___x_1536_);
                            lean_dec_ref(v___x_1535_);
                            lean_dec_ref(v___x_1534_);
                            v___x_1775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                            return v___x_1775_;
                        } else {
                            v___x_1776_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1548_);
                            lean_dec(v___x_1771_);
                            v_args_1777_ = l_Lean_Syntax_getArgs(v___x_1776_);
                            lean_dec(v___x_1776_);
                            v___x_1778_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1778_, 0, v_args_1777_);
                            v___y_1736_ = v_o_1757_;
                            v_args_1737_ = v___x_1778_;
                            v___y_1738_ = v___y_1758_;
                            v___y_1739_ = v___y_1759_;
                            v___y_1740_ = v___y_1760_;
                            v___y_1741_ = v___y_1761_;
                            v___y_1742_ = v___y_1762_;
                            v___y_1743_ = v___y_1763_;
                            v___y_1744_ = v___y_1764_;
                            v___y_1745_ = v___y_1765_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1767_);
                    v___x_1779_ = lean_box(0);
                    v___y_1736_ = v_o_1757_;
                    v_args_1737_ = v___x_1779_;
                    v___y_1738_ = v___y_1758_;
                    v___y_1739_ = v___y_1759_;
                    v___y_1740_ = v___y_1760_;
                    v___y_1741_ = v___y_1761_;
                    v___y_1742_ = v___y_1762_;
                    v___y_1743_ = v___y_1763_;
                    v___y_1744_ = v___y_1764_;
                    v___y_1745_ = v___y_1765_;
                    state = 17;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(
    mut v___x_1788_: *mut LeanObject,
    mut v_stx_1789_: *mut LeanObject,
    mut v___x_1790_: *mut LeanObject,
    mut v___x_1791_: *mut LeanObject,
    mut v___x_1792_: *mut LeanObject,
    mut v___x_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6219__boxed_1803_: u8 = 0;
    let mut v___x_6223__boxed_1804_: u8 = 0;
    let mut v_res_1805_: *mut LeanObject = core::ptr::null_mut();
    v___x_6219__boxed_1803_ = (lean_unbox(v___x_1788_) as u8);
    v___x_6223__boxed_1804_ = (lean_unbox(v___x_1793_) as u8);
    v_res_1805_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(
        v___x_6219__boxed_1803_,
        v_stx_1789_,
        v___x_1790_,
        v___x_1791_,
        v___x_1792_,
        v___x_6223__boxed_1804_,
        v___y_1794_,
        v___y_1795_,
        v___y_1796_,
        v___y_1797_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        v___y_1801_,
    );
    lean_dec(v___y_1801_);
    lean_dec_ref(v___y_1800_);
    lean_dec(v___y_1799_);
    lean_dec_ref(v___y_1798_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    lean_dec(v___y_1795_);
    lean_dec_ref(v___y_1794_);
    lean_dec(v_stx_1789_);
    return v_res_1805_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace(
    mut v_stx_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1823_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0;
    v___x_1824_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1;
    v___x_1825_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2;
    v___x_1826_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1;
    lean_inc(v_stx_1813_);
    v___x_1827_ = l_Lean_Syntax_isOfKind(v_stx_1813_, v___x_1826_);
    v___x_1828_ = 1;
    v___x_1829_ = lean_box((v___x_1827_) as usize);
    v___x_1830_ = lean_box((v___x_1828_) as usize);
    v___y_1831_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    lean_closure_set(v___y_1831_, 0, v___x_1829_);
    lean_closure_set(v___y_1831_, 1, v_stx_1813_);
    lean_closure_set(v___y_1831_, 2, v___x_1823_);
    lean_closure_set(v___y_1831_, 3, v___x_1824_);
    lean_closure_set(v___y_1831_, 4, v___x_1825_);
    lean_closure_set(v___y_1831_, 5, v___x_1830_);
    v___x_1832_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_1831_,
        v_a_1814_,
        v_a_1815_,
        v_a_1816_,
        v_a_1817_,
        v_a_1818_,
        v_a_1819_,
        v_a_1820_,
        v_a_1821_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(
    mut v_stx_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1843_: *mut LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(
        v_stx_1833_,
        v_a_1834_,
        v_a_1835_,
        v_a_1836_,
        v_a_1837_,
        v_a_1838_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
    );
    lean_dec(v_a_1841_);
    lean_dec_ref(v_a_1840_);
    lean_dec(v_a_1839_);
    lean_dec_ref(v_a_1838_);
    lean_dec(v_a_1837_);
    lean_dec_ref(v_a_1836_);
    lean_dec(v_a_1835_);
    lean_dec_ref(v_a_1834_);
    return v_res_1843_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1()
-> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1853_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1;
    v___x_1854_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1;
    v___x_1855_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1856_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1852_,
        v___x_1853_,
        v___x_1854_,
        v___x_1855_,
    );
    return v___x_1856_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(
    mut v_a_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
    return v_res_1858_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_a_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1868_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_1860_,
                    v___y_1863_,
                    v___y_1864_,
                    v___y_1865_,
                    v___y_1866_,
                );
                if lean_obj_tag(v___x_1868_) == 0 {
                    v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
                    lean_inc(v_a_1869_);
                    lean_dec_ref_known(v___x_1868_, 1);
                    v___x_1870_ = l_Lean_Meta_Split_simpMatch(
                        v_a_1869_,
                        v___y_1863_,
                        v___y_1864_,
                        v___y_1865_,
                        v___y_1866_,
                    );
                    if lean_obj_tag(v___x_1870_) == 0 {
                        v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
                        lean_inc(v_a_1871_);
                        lean_dec_ref_known(v___x_1870_, 1);
                        v___x_1872_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                            v_a_1871_,
                            v___y_1859_,
                            v___y_1860_,
                            v___y_1861_,
                            v___y_1862_,
                            v___y_1863_,
                            v___y_1864_,
                            v___y_1865_,
                            v___y_1866_,
                        );
                        return v___x_1872_;
                    } else {
                        v_a_1873_ = lean_ctor_get(v___x_1870_, 0);
                        v_isSharedCheck_1880_ = (!lean_is_exclusive(v___x_1870_)) as u8;
                        if v_isSharedCheck_1880_ == 0 {
                            v___x_1875_ = v___x_1870_;
                            v_isShared_1876_ = v_isSharedCheck_1880_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1873_);
                            lean_dec(v___x_1870_);
                            v___x_1875_ = lean_box(0);
                            v_isShared_1876_ = v_isSharedCheck_1880_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1881_ = lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1888_ = (!lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1888_ == 0 {
                        v___x_1883_ = v___x_1868_;
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1881_);
                        lean_dec(v___x_1868_);
                        v___x_1883_ = lean_box(0);
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1876_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1878_;
            }
            3 => {
                if v_isShared_1884_ == 0 {
                    v___x_1886_ = v___x_1883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
                    v___x_1886_ = v_reuseFailAlloc_1887_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1898_: *mut LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(
        v___y_1889_,
        v___y_1890_,
        v___y_1891_,
        v___y_1892_,
        v___y_1893_,
        v___y_1894_,
        v___y_1895_,
        v___y_1896_,
    );
    lean_dec(v___y_1896_);
    lean_dec_ref(v___y_1895_);
    lean_dec(v___y_1894_);
    lean_dec_ref(v___y_1893_);
    lean_dec(v___y_1892_);
    lean_dec_ref(v___y_1891_);
    lean_dec(v___y_1890_);
    lean_dec_ref(v___y_1889_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___f_1909_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0;
    v___x_1910_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1909_,
        v_a_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
        v_a_1904_,
        v_a_1905_,
        v_a_1906_,
        v_a_1907_,
    );
    return v___x_1910_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(
    mut v_a_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
    mut v_a_1916_: *mut LeanObject,
    mut v_a_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
        v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_,
    );
    lean_dec(v_a_1918_);
    lean_dec_ref(v_a_1917_);
    lean_dec(v_a_1916_);
    lean_dec_ref(v_a_1915_);
    lean_dec(v_a_1914_);
    lean_dec_ref(v_a_1913_);
    lean_dec(v_a_1912_);
    lean_dec_ref(v_a_1911_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch(
    mut v_x_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
    mut v_a_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
        v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_,
    );
    return v___x_1931_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(
    mut v_x_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
    mut v_a_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1942_: *mut LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(
        v_x_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_,
        v_a_1940_,
    );
    lean_dec(v_a_1940_);
    lean_dec_ref(v_a_1939_);
    lean_dec(v_a_1938_);
    lean_dec_ref(v_a_1937_);
    lean_dec(v_a_1936_);
    lean_dec_ref(v_a_1935_);
    lean_dec(v_a_1934_);
    lean_dec_ref(v_a_1933_);
    lean_dec(v_x_1932_);
    return v_res_1942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1()
-> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1959_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1;
    v___x_1960_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3;
    v___x_1961_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1962_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1958_,
        v___x_1959_,
        v___x_1960_,
        v___x_1961_,
    );
    return v___x_1962_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_res_1964_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
    return v_res_1964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3()
-> *mut LeanObject {
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1991_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3;
    v___x_1992_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6;
    v___x_1993_ = l_Lean_addBuiltinDeclarationRanges(v___x_1991_, v___x_1992_);
    return v___x_1993_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(
    mut v_a_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1995_: *mut LeanObject = core::ptr::null_mut();
    v_res_1995_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
    return v_res_1995_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(
    mut v_stx_1998_: *mut LeanObject,
    mut v___x_1999_: u8,
    mut v___x_2000_: u8,
    mut v___x_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2029_: u8 = 0;
    let mut v_a_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_a_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v_stx_1998_,
                    v___x_1999_,
                    v___x_2000_,
                    v___x_1999_,
                    v___x_2001_,
                    v___y_2002_,
                    v___y_2003_,
                    v___y_2004_,
                    v___y_2005_,
                    v___y_2006_,
                    v___y_2007_,
                    v___y_2008_,
                    v___y_2009_,
                );
                if lean_obj_tag(v___x_2011_) == 0 {
                    v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
                    lean_inc(v_a_2012_);
                    lean_dec_ref_known(v___x_2011_, 1);
                    v_ctx_2013_ = lean_ctor_get(v_a_2012_, 0);
                    lean_inc_ref(v_ctx_2013_);
                    lean_dec(v_a_2012_);
                    v___x_2014_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_2003_,
                        v___y_2006_,
                        v___y_2007_,
                        v___y_2008_,
                        v___y_2009_,
                    );
                    if lean_obj_tag(v___x_2014_) == 0 {
                        v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
                        lean_inc(v_a_2015_);
                        lean_dec_ref_known(v___x_2014_, 1);
                        v___x_2016_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0;
                        v___x_2017_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
                        );
                        v___x_2018_ = l_Lean_Meta_dsimp(
                            v_a_2015_,
                            v_ctx_2013_,
                            v___x_2016_,
                            v___x_2017_,
                            v___y_2006_,
                            v___y_2007_,
                            v___y_2008_,
                            v___y_2009_,
                        );
                        if lean_obj_tag(v___x_2018_) == 0 {
                            v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
                            lean_inc(v_a_2019_);
                            lean_dec_ref_known(v___x_2018_, 1);
                            v_fst_2020_ = lean_ctor_get(v_a_2019_, 0);
                            lean_inc(v_fst_2020_);
                            lean_dec(v_a_2019_);
                            v___x_2021_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_fst_2020_,
                                v___y_2002_,
                                v___y_2003_,
                                v___y_2004_,
                                v___y_2005_,
                                v___y_2006_,
                                v___y_2007_,
                                v___y_2008_,
                                v___y_2009_,
                            );
                            return v___x_2021_;
                        } else {
                            v_a_2022_ = lean_ctor_get(v___x_2018_, 0);
                            v_isSharedCheck_2029_ = (!lean_is_exclusive(v___x_2018_)) as u8;
                            if v_isSharedCheck_2029_ == 0 {
                                v___x_2024_ = v___x_2018_;
                                v_isShared_2025_ = v_isSharedCheck_2029_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2022_);
                                lean_dec(v___x_2018_);
                                v___x_2024_ = lean_box(0);
                                v_isShared_2025_ = v_isSharedCheck_2029_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_ctx_2013_);
                        v_a_2030_ = lean_ctor_get(v___x_2014_, 0);
                        v_isSharedCheck_2037_ = (!lean_is_exclusive(v___x_2014_)) as u8;
                        if v_isSharedCheck_2037_ == 0 {
                            v___x_2032_ = v___x_2014_;
                            v_isShared_2033_ = v_isSharedCheck_2037_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2030_);
                            lean_dec(v___x_2014_);
                            v___x_2032_ = lean_box(0);
                            v_isShared_2033_ = v_isSharedCheck_2037_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2038_ = lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2045_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2040_ = v___x_2011_;
                        v_isShared_2041_ = v_isSharedCheck_2045_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2038_);
                        lean_dec(v___x_2011_);
                        v___x_2040_ = lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2045_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2025_ == 0 {
                    v___x_2027_ = v___x_2024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
                    v___x_2027_ = v_reuseFailAlloc_2028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2027_;
            }
            3 => {
                if v_isShared_2033_ == 0 {
                    v___x_2035_ = v___x_2032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
                    v___x_2035_ = v_reuseFailAlloc_2036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2035_;
            }
            5 => {
                if v_isShared_2041_ == 0 {
                    v___x_2043_ = v___x_2040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(
    mut v_stx_2046_: *mut LeanObject,
    mut v___x_2047_: *mut LeanObject,
    mut v___x_2048_: *mut LeanObject,
    mut v___x_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_586__boxed_2059_: u8 = 0;
    let mut v___x_587__boxed_2060_: u8 = 0;
    let mut v_res_2061_: *mut LeanObject = core::ptr::null_mut();
    v___x_586__boxed_2059_ = (lean_unbox(v___x_2047_) as u8);
    v___x_587__boxed_2060_ = (lean_unbox(v___x_2048_) as u8);
    v_res_2061_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(
        v_stx_2046_,
        v___x_586__boxed_2059_,
        v___x_587__boxed_2060_,
        v___x_2049_,
        v___y_2050_,
        v___y_2051_,
        v___y_2052_,
        v___y_2053_,
        v___y_2054_,
        v___y_2055_,
        v___y_2056_,
        v___y_2057_,
    );
    lean_dec(v___y_2057_);
    lean_dec_ref(v___y_2056_);
    lean_dec(v___y_2055_);
    lean_dec_ref(v___y_2054_);
    lean_dec(v___y_2053_);
    lean_dec_ref(v___y_2052_);
    lean_dec(v___y_2051_);
    lean_dec_ref(v___y_2050_);
    lean_dec(v_stx_2046_);
    return v_res_2061_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp(
    mut v_stx_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
    mut v_a_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2072_ = 0;
    v___x_2073_ = 2;
    v___x_2074_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
    v___x_2075_ = lean_box((v___x_2072_) as usize);
    v___x_2076_ = lean_box((v___x_2073_) as usize);
    v___f_2077_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_2077_, 0, v_stx_2062_);
    lean_closure_set(v___f_2077_, 1, v___x_2075_);
    lean_closure_set(v___f_2077_, 2, v___x_2076_);
    lean_closure_set(v___f_2077_, 3, v___x_2074_);
    v___x_2078_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_2077_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
        v_a_2067_,
        v_a_2068_,
        v_a_2069_,
        v_a_2070_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(
    mut v_stx_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2089_: *mut LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_Lean_Elab_Tactic_Conv_evalDSimp(
        v_stx_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
        v_a_2086_,
        v_a_2087_,
    );
    lean_dec(v_a_2087_);
    lean_dec_ref(v_a_2086_);
    lean_dec(v_a_2085_);
    lean_dec_ref(v_a_2084_);
    lean_dec(v_a_2083_);
    lean_dec_ref(v_a_2082_);
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    return v_res_2089_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1()
-> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2106_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1;
    v___x_2107_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3;
    v___x_2108_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2109_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2105_,
        v___x_2106_,
        v___x_2107_,
        v___x_2108_,
    );
    return v___x_2109_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
    return v_res_2111_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3()
-> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    v___x_2137_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3;
    v___x_2138_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6;
    v___x_2139_ = l_Lean_addBuiltinDeclarationRanges(v___x_2137_, v___x_2138_);
    return v___x_2139_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(
    mut v_a_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_res_2141_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
    return v_res_2141_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(
    mut v___x_2143_: u8,
    mut v_stx_2144_: *mut LeanObject,
    mut v___x_2145_: *mut LeanObject,
    mut v___x_2146_: *mut LeanObject,
    mut v___x_2147_: *mut LeanObject,
    mut v___x_2148_: u8,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: u8 = 0;
    let mut v___y_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v_usedTheorems_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2209_: u8 = 0;
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_unused_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_unused_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v___y_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: u8 = 0;
    let mut v___y_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_o_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2143_ == 0 {
                    lean_dec_ref(v___x_2147_);
                    lean_dec_ref(v___x_2146_);
                    lean_dec_ref(v___x_2145_);
                    v___x_2158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                    return v___x_2158_;
                } else {
                    v___x_2159_ = lean_unsigned_to_nat(1);
                    v___x_2160_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2159_);
                    v___x_2161_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0;
                    lean_inc_ref(v___x_2147_);
                    lean_inc_ref(v___x_2146_);
                    lean_inc_ref(v___x_2145_);
                    v___x_2162_ =
                        l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2161_);
                    lean_inc(v___x_2160_);
                    v___x_2163_ = l_Lean_Syntax_isOfKind(v___x_2160_, v___x_2162_);
                    lean_dec(v___x_2162_);
                    if v___x_2163_ == 0 {
                        lean_dec(v___x_2160_);
                        lean_dec_ref(v___x_2147_);
                        lean_dec_ref(v___x_2146_);
                        lean_dec_ref(v___x_2145_);
                        v___x_2164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_2164_;
                    } else {
                        v___x_2165_ = lean_unsigned_to_nat(0);
                        v_tk_2166_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2165_);
                        v___x_2342_ = lean_unsigned_to_nat(2);
                        v___x_2343_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2342_);
                        v___x_2344_ = l_Lean_Syntax_isNone(v___x_2343_);
                        if v___x_2344_ == 0 {
                            lean_inc(v___x_2343_);
                            v___x_2345_ = l_Lean_Syntax_matchesNull(v___x_2343_, v___x_2159_);
                            if v___x_2345_ == 0 {
                                lean_dec(v___x_2343_);
                                lean_dec(v_tk_2166_);
                                lean_dec(v___x_2160_);
                                lean_dec_ref(v___x_2147_);
                                lean_dec_ref(v___x_2146_);
                                lean_dec_ref(v___x_2145_);
                                v___x_2346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                                return v___x_2346_;
                            } else {
                                v_o_2347_ = l_Lean_Syntax_getArg(v___x_2343_, v___x_2165_);
                                lean_dec(v___x_2343_);
                                v___x_2348_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2348_, 0, v_o_2347_);
                                v_o_2319_ = v___x_2348_;
                                v___y_2320_ = v___y_2149_;
                                v___y_2321_ = v___y_2150_;
                                v___y_2322_ = v___y_2151_;
                                v___y_2323_ = v___y_2152_;
                                v___y_2324_ = v___y_2153_;
                                v___y_2325_ = v___y_2154_;
                                v___y_2326_ = v___y_2155_;
                                v___y_2327_ = v___y_2156_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_2343_);
                            v___x_2349_ = lean_box(0);
                            v_o_2319_ = v___x_2349_;
                            v___y_2320_ = v___y_2149_;
                            v___y_2321_ = v___y_2150_;
                            v___y_2322_ = v___y_2151_;
                            v___y_2323_ = v___y_2152_;
                            v___y_2324_ = v___y_2153_;
                            v___y_2325_ = v___y_2154_;
                            v___y_2326_ = v___y_2155_;
                            v___y_2327_ = v___y_2156_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2177_);
                v___x_2186_ = l_Array_append___redArg(v___y_2177_, v___y_2185_);
                lean_dec_ref(v___y_2185_);
                lean_inc(v___y_2180_);
                lean_inc(v___y_2182_);
                v___x_2187_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2187_, 0, v___y_2182_);
                lean_ctor_set(v___x_2187_, 1, v___y_2180_);
                lean_ctor_set(v___x_2187_, 2, v___x_2186_);
                lean_inc(v___y_2171_);
                v___x_2188_ = l_Lean_Syntax_node6(
                    v___y_2182_,
                    v___y_2176_,
                    v___y_2184_,
                    v___x_2160_,
                    v___y_2171_,
                    v___y_2168_,
                    v___x_2187_,
                    v___y_2171_,
                );
                v___x_2189_ = 2;
                v___x_2190_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
                v___x_2191_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___x_2188_,
                    v___y_2172_,
                    v___x_2189_,
                    v___y_2172_,
                    v___x_2190_,
                    v___y_2181_,
                    v___y_2179_,
                    v___y_2169_,
                    v___y_2173_,
                    v___y_2178_,
                    v___y_2175_,
                    v___y_2183_,
                    v___y_2174_,
                );
                if lean_obj_tag(v___x_2191_) == 0 {
                    v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
                    lean_inc(v_a_2192_);
                    lean_dec_ref_known(v___x_2191_, 1);
                    v_ctx_2193_ = lean_ctor_get(v_a_2192_, 0);
                    lean_inc_ref(v_ctx_2193_);
                    lean_dec(v_a_2192_);
                    v___x_2194_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_2179_,
                        v___y_2178_,
                        v___y_2175_,
                        v___y_2183_,
                        v___y_2174_,
                    );
                    if lean_obj_tag(v___x_2194_) == 0 {
                        v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
                        lean_inc(v_a_2195_);
                        lean_dec_ref_known(v___x_2194_, 1);
                        v___x_2196_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0;
                        v___x_2197_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
                        );
                        v___x_2198_ = l_Lean_Meta_dsimp(
                            v_a_2195_,
                            v_ctx_2193_,
                            v___x_2196_,
                            v___x_2197_,
                            v___y_2178_,
                            v___y_2175_,
                            v___y_2183_,
                            v___y_2174_,
                        );
                        if lean_obj_tag(v___x_2198_) == 0 {
                            v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
                            lean_inc(v_a_2199_);
                            lean_dec_ref_known(v___x_2198_, 1);
                            v_fst_2200_ = lean_ctor_get(v_a_2199_, 0);
                            lean_inc(v_fst_2200_);
                            v_snd_2201_ = lean_ctor_get(v_a_2199_, 1);
                            lean_inc(v_snd_2201_);
                            lean_dec(v_a_2199_);
                            v___x_2202_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_fst_2200_,
                                v___y_2181_,
                                v___y_2179_,
                                v___y_2169_,
                                v___y_2173_,
                                v___y_2178_,
                                v___y_2175_,
                                v___y_2183_,
                                v___y_2174_,
                            );
                            if lean_obj_tag(v___x_2202_) == 0 {
                                v_isSharedCheck_2235_ = (!lean_is_exclusive(v___x_2202_)) as u8;
                                if v_isSharedCheck_2235_ == 0 {
                                    v_unused_2236_ = lean_ctor_get(v___x_2202_, 0);
                                    lean_dec(v_unused_2236_);
                                    v___x_2204_ = v___x_2202_;
                                    v_isShared_2205_ = v_isSharedCheck_2235_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v___x_2202_);
                                    v___x_2204_ = lean_box(0);
                                    v_isShared_2205_ = v_isSharedCheck_2235_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_2201_);
                                lean_dec(v___x_2188_);
                                lean_dec(v_tk_2166_);
                                return v___x_2202_;
                            }
                        } else {
                            lean_dec(v___x_2188_);
                            lean_dec(v_tk_2166_);
                            v_a_2237_ = lean_ctor_get(v___x_2198_, 0);
                            v_isSharedCheck_2244_ = (!lean_is_exclusive(v___x_2198_)) as u8;
                            if v_isSharedCheck_2244_ == 0 {
                                v___x_2239_ = v___x_2198_;
                                v_isShared_2240_ = v_isSharedCheck_2244_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2237_);
                                lean_dec(v___x_2198_);
                                v___x_2239_ = lean_box(0);
                                v_isShared_2240_ = v_isSharedCheck_2244_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_ctx_2193_);
                        lean_dec(v___x_2188_);
                        lean_dec(v_tk_2166_);
                        v_a_2245_ = lean_ctor_get(v___x_2194_, 0);
                        v_isSharedCheck_2252_ = (!lean_is_exclusive(v___x_2194_)) as u8;
                        if v_isSharedCheck_2252_ == 0 {
                            v___x_2247_ = v___x_2194_;
                            v_isShared_2248_ = v_isSharedCheck_2252_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2245_);
                            lean_dec(v___x_2194_);
                            v___x_2247_ = lean_box(0);
                            v_isShared_2248_ = v_isSharedCheck_2252_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2188_);
                    lean_dec(v_tk_2166_);
                    v_a_2253_ = lean_ctor_get(v___x_2191_, 0);
                    v_isSharedCheck_2260_ = (!lean_is_exclusive(v___x_2191_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2255_ = v___x_2191_;
                        v_isShared_2256_ = v_isSharedCheck_2260_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2253_);
                        lean_dec(v___x_2191_);
                        v___x_2255_ = lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2260_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_usedTheorems_2206_ = lean_ctor_get(v_snd_2201_, 0);
                v_isSharedCheck_2233_ = (!lean_is_exclusive(v_snd_2201_)) as u8;
                if v_isSharedCheck_2233_ == 0 {
                    v_unused_2234_ = lean_ctor_get(v_snd_2201_, 1);
                    lean_dec(v_unused_2234_);
                    v___x_2208_ = v_snd_2201_;
                    v_isShared_2209_ = v_isSharedCheck_2233_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_usedTheorems_2206_);
                    lean_dec(v_snd_2201_);
                    v___x_2208_ = lean_box(0);
                    v_isShared_2209_ = v_isSharedCheck_2233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2210_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___x_2188_,
                    v_usedTheorems_2206_,
                    v___y_2178_,
                    v___y_2175_,
                    v___y_2183_,
                    v___y_2174_,
                );
                lean_dec_ref(v_usedTheorems_2206_);
                if lean_obj_tag(v___x_2210_) == 0 {
                    v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
                    lean_inc(v_a_2211_);
                    lean_dec_ref_known(v___x_2210_, 1);
                    v___x_2212_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2;
                    if v_isShared_2209_ == 0 {
                        lean_ctor_set(v___x_2208_, 1, v_a_2211_);
                        lean_ctor_set(v___x_2208_, 0, v___x_2212_);
                        v___x_2214_ = v___x_2208_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2212_);
                        lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2211_);
                        v___x_2214_ = v_reuseFailAlloc_2224_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2208_);
                    lean_del_object(v___x_2204_);
                    lean_dec(v_tk_2166_);
                    v_a_2225_ = lean_ctor_get(v___x_2210_, 0);
                    v_isSharedCheck_2232_ = (!lean_is_exclusive(v___x_2210_)) as u8;
                    if v_isSharedCheck_2232_ == 0 {
                        v___x_2227_ = v___x_2210_;
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2225_);
                        lean_dec(v___x_2210_);
                        v___x_2227_ = lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2215_ = lean_box(0);
                v___x_2216_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2216_, 0, v___x_2214_);
                lean_ctor_set(v___x_2216_, 1, v___x_2215_);
                lean_ctor_set(v___x_2216_, 2, v___x_2215_);
                lean_ctor_set(v___x_2216_, 3, v___x_2215_);
                lean_ctor_set(v___x_2216_, 4, v___x_2215_);
                lean_ctor_set(v___x_2216_, 5, v___x_2215_);
                lean_inc(v___y_2170_);
                if v_isShared_2205_ == 0 {
                    lean_ctor_set_tag(v___x_2204_, 1);
                    lean_ctor_set(v___x_2204_, 0, v___y_2170_);
                    v___x_2218_ = v___x_2204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___y_2170_);
                    v___x_2218_ = v_reuseFailAlloc_2223_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2219_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3;
                v___x_2220_ = 4;
                v___x_2221_ = l_Lean_MessageData_nil;
                v___x_2222_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_2166_,
                    v___x_2216_,
                    v___x_2218_,
                    v___x_2219_,
                    v___x_2215_,
                    v___x_2220_,
                    v___x_2221_,
                    v___y_2183_,
                    v___y_2174_,
                );
                return v___x_2222_;
            }
            6 => {
                if v_isShared_2228_ == 0 {
                    v___x_2230_ = v___x_2227_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
                    v___x_2230_ = v_reuseFailAlloc_2231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2230_;
            }
            8 => {
                if v_isShared_2240_ == 0 {
                    v___x_2242_ = v___x_2239_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
                    v___x_2242_ = v_reuseFailAlloc_2243_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2242_;
            }
            10 => {
                if v_isShared_2248_ == 0 {
                    v___x_2250_ = v___x_2247_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2250_;
            }
            12 => {
                if v_isShared_2256_ == 0 {
                    v___x_2258_ = v___x_2255_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2258_;
            }
            14 => {
                lean_inc_ref(v___y_2270_);
                v___x_2280_ = l_Array_append___redArg(v___y_2270_, v___y_2279_);
                lean_dec_ref(v___y_2279_);
                lean_inc(v___y_2273_);
                lean_inc(v___y_2276_);
                v___x_2281_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2281_, 0, v___y_2276_);
                lean_ctor_set(v___x_2281_, 1, v___y_2273_);
                lean_ctor_set(v___x_2281_, 2, v___x_2280_);
                if lean_obj_tag(v___y_2275_) == 1 {
                    v_val_2282_ = lean_ctor_get(v___y_2275_, 0);
                    lean_inc(v_val_2282_);
                    lean_dec_ref_known(v___y_2275_, 1);
                    v___x_2283_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4;
                    lean_inc_n(v___y_2276_, 3);
                    v___x_2284_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2284_, 0, v___y_2276_);
                    lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                    lean_inc_ref(v___y_2270_);
                    v___x_2285_ = l_Array_append___redArg(v___y_2270_, v_val_2282_);
                    lean_dec(v_val_2282_);
                    lean_inc(v___y_2273_);
                    v___x_2286_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2286_, 0, v___y_2276_);
                    lean_ctor_set(v___x_2286_, 1, v___y_2273_);
                    lean_ctor_set(v___x_2286_, 2, v___x_2285_);
                    v___x_2287_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5;
                    v___x_2288_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2288_, 0, v___y_2276_);
                    lean_ctor_set(v___x_2288_, 1, v___x_2287_);
                    v___x_2289_ = l_Array_mkArray3___redArg(v___x_2284_, v___x_2286_, v___x_2288_);
                    v___y_2168_ = v___x_2281_;
                    v___y_2169_ = v___y_2262_;
                    v___y_2170_ = v___y_2263_;
                    v___y_2171_ = v___y_2264_;
                    v___y_2172_ = v___y_2265_;
                    v___y_2173_ = v___y_2266_;
                    v___y_2174_ = v___y_2267_;
                    v___y_2175_ = v___y_2268_;
                    v___y_2176_ = v___y_2269_;
                    v___y_2177_ = v___y_2270_;
                    v___y_2178_ = v___y_2271_;
                    v___y_2179_ = v___y_2272_;
                    v___y_2180_ = v___y_2273_;
                    v___y_2181_ = v___y_2274_;
                    v___y_2182_ = v___y_2276_;
                    v___y_2183_ = v___y_2278_;
                    v___y_2184_ = v___y_2277_;
                    v___y_2185_ = v___x_2289_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_2275_);
                    v___x_2290_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_2168_ = v___x_2281_;
                    v___y_2169_ = v___y_2262_;
                    v___y_2170_ = v___y_2263_;
                    v___y_2171_ = v___y_2264_;
                    v___y_2172_ = v___y_2265_;
                    v___y_2173_ = v___y_2266_;
                    v___y_2174_ = v___y_2267_;
                    v___y_2175_ = v___y_2268_;
                    v___y_2176_ = v___y_2269_;
                    v___y_2177_ = v___y_2270_;
                    v___y_2178_ = v___y_2271_;
                    v___y_2179_ = v___y_2272_;
                    v___y_2180_ = v___y_2273_;
                    v___y_2181_ = v___y_2274_;
                    v___y_2182_ = v___y_2276_;
                    v___y_2183_ = v___y_2278_;
                    v___y_2184_ = v___y_2277_;
                    v___y_2185_ = v___x_2290_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                v_ref_2302_ = lean_ctor_get(v___y_2300_, 5);
                v___x_2303_ = 0;
                v___x_2304_ = l_Lean_SourceInfo_fromRef(v_ref_2302_, v___x_2303_);
                v___x_2305_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0;
                v___x_2306_ =
                    l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2305_);
                v___x_2307_ = l_Lean_SourceInfo_fromRef(v_tk_2166_, v___x_2148_);
                v___x_2308_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                lean_ctor_set(v___x_2308_, 1, v___x_2305_);
                v___x_2309_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9;
                v___x_2310_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10,
                );
                lean_inc(v___x_2304_);
                v___x_2311_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2311_, 0, v___x_2304_);
                lean_ctor_set(v___x_2311_, 1, v___x_2309_);
                lean_ctor_set(v___x_2311_, 2, v___x_2310_);
                if lean_obj_tag(v___y_2292_) == 1 {
                    v_val_2312_ = lean_ctor_get(v___y_2292_, 0);
                    lean_inc(v_val_2312_);
                    lean_dec_ref_known(v___y_2292_, 1);
                    v___x_2313_ = l_Lean_SourceInfo_fromRef(v_val_2312_, v___x_2148_);
                    lean_dec(v_val_2312_);
                    v___x_2314_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7;
                    v___x_2315_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Array_mkArray1___redArg(v___x_2315_);
                    v___y_2262_ = v___y_2296_;
                    v___y_2263_ = v_ref_2302_;
                    v___y_2264_ = v___x_2311_;
                    v___y_2265_ = v___x_2303_;
                    v___y_2266_ = v___y_2297_;
                    v___y_2267_ = v___y_2301_;
                    v___y_2268_ = v___y_2299_;
                    v___y_2269_ = v___x_2306_;
                    v___y_2270_ = v___x_2310_;
                    v___y_2271_ = v___y_2298_;
                    v___y_2272_ = v___y_2295_;
                    v___y_2273_ = v___x_2309_;
                    v___y_2274_ = v___y_2294_;
                    v___y_2275_ = v_args_2293_;
                    v___y_2276_ = v___x_2304_;
                    v___y_2277_ = v___x_2308_;
                    v___y_2278_ = v___y_2300_;
                    v___y_2279_ = v___x_2316_;
                    state = 14;
                    continue;
                } else {
                    lean_dec(v___y_2292_);
                    v___x_2317_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_2262_ = v___y_2296_;
                    v___y_2263_ = v_ref_2302_;
                    v___y_2264_ = v___x_2311_;
                    v___y_2265_ = v___x_2303_;
                    v___y_2266_ = v___y_2297_;
                    v___y_2267_ = v___y_2301_;
                    v___y_2268_ = v___y_2299_;
                    v___y_2269_ = v___x_2306_;
                    v___y_2270_ = v___x_2310_;
                    v___y_2271_ = v___y_2298_;
                    v___y_2272_ = v___y_2295_;
                    v___y_2273_ = v___x_2309_;
                    v___y_2274_ = v___y_2294_;
                    v___y_2275_ = v_args_2293_;
                    v___y_2276_ = v___x_2304_;
                    v___y_2277_ = v___x_2308_;
                    v___y_2278_ = v___y_2300_;
                    v___y_2279_ = v___x_2317_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_2328_ = lean_unsigned_to_nat(3);
                v___x_2329_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2328_);
                v___x_2330_ = l_Lean_Syntax_isNone(v___x_2329_);
                if v___x_2330_ == 0 {
                    lean_inc(v___x_2329_);
                    v___x_2331_ = l_Lean_Syntax_matchesNull(v___x_2329_, v___x_2159_);
                    if v___x_2331_ == 0 {
                        lean_dec(v___x_2329_);
                        lean_dec(v_o_2319_);
                        lean_dec(v_tk_2166_);
                        lean_dec(v___x_2160_);
                        lean_dec_ref(v___x_2147_);
                        lean_dec_ref(v___x_2146_);
                        lean_dec_ref(v___x_2145_);
                        v___x_2332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_2332_;
                    } else {
                        v___x_2333_ = l_Lean_Syntax_getArg(v___x_2329_, v___x_2165_);
                        lean_dec(v___x_2329_);
                        v___x_2334_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0;
                        lean_inc_ref(v___x_2147_);
                        lean_inc_ref(v___x_2146_);
                        lean_inc_ref(v___x_2145_);
                        v___x_2335_ =
                            l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2334_);
                        lean_inc(v___x_2333_);
                        v___x_2336_ = l_Lean_Syntax_isOfKind(v___x_2333_, v___x_2335_);
                        lean_dec(v___x_2335_);
                        if v___x_2336_ == 0 {
                            lean_dec(v___x_2333_);
                            lean_dec(v_o_2319_);
                            lean_dec(v_tk_2166_);
                            lean_dec(v___x_2160_);
                            lean_dec_ref(v___x_2147_);
                            lean_dec_ref(v___x_2146_);
                            lean_dec_ref(v___x_2145_);
                            v___x_2337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                            return v___x_2337_;
                        } else {
                            v___x_2338_ = l_Lean_Syntax_getArg(v___x_2333_, v___x_2159_);
                            lean_dec(v___x_2333_);
                            v_args_2339_ = l_Lean_Syntax_getArgs(v___x_2338_);
                            lean_dec(v___x_2338_);
                            v___x_2340_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2340_, 0, v_args_2339_);
                            v___y_2292_ = v_o_2319_;
                            v_args_2293_ = v___x_2340_;
                            v___y_2294_ = v___y_2320_;
                            v___y_2295_ = v___y_2321_;
                            v___y_2296_ = v___y_2322_;
                            v___y_2297_ = v___y_2323_;
                            v___y_2298_ = v___y_2324_;
                            v___y_2299_ = v___y_2325_;
                            v___y_2300_ = v___y_2326_;
                            v___y_2301_ = v___y_2327_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2329_);
                    v___x_2341_ = lean_box(0);
                    v___y_2292_ = v_o_2319_;
                    v_args_2293_ = v___x_2341_;
                    v___y_2294_ = v___y_2320_;
                    v___y_2295_ = v___y_2321_;
                    v___y_2296_ = v___y_2322_;
                    v___y_2297_ = v___y_2323_;
                    v___y_2298_ = v___y_2324_;
                    v___y_2299_ = v___y_2325_;
                    v___y_2300_ = v___y_2326_;
                    v___y_2301_ = v___y_2327_;
                    state = 15;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(
    mut v___x_2350_: *mut LeanObject,
    mut v_stx_2351_: *mut LeanObject,
    mut v___x_2352_: *mut LeanObject,
    mut v___x_2353_: *mut LeanObject,
    mut v___x_2354_: *mut LeanObject,
    mut v___x_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5500__boxed_2365_: u8 = 0;
    let mut v___x_5504__boxed_2366_: u8 = 0;
    let mut v_res_2367_: *mut LeanObject = core::ptr::null_mut();
    v___x_5500__boxed_2365_ = (lean_unbox(v___x_2350_) as u8);
    v___x_5504__boxed_2366_ = (lean_unbox(v___x_2355_) as u8);
    v_res_2367_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(
        v___x_5500__boxed_2365_,
        v_stx_2351_,
        v___x_2352_,
        v___x_2353_,
        v___x_2354_,
        v___x_5504__boxed_2366_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
        v___y_2359_,
        v___y_2360_,
        v___y_2361_,
        v___y_2362_,
        v___y_2363_,
    );
    lean_dec(v___y_2363_);
    lean_dec_ref(v___y_2362_);
    lean_dec(v___y_2361_);
    lean_dec_ref(v___y_2360_);
    lean_dec(v___y_2359_);
    lean_dec_ref(v___y_2358_);
    lean_dec(v___y_2357_);
    lean_dec_ref(v___y_2356_);
    lean_dec(v_stx_2351_);
    return v_res_2367_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace(
    mut v_stx_2375_: *mut LeanObject,
    mut v_a_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_a_2378_: *mut LeanObject,
    mut v_a_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    v___x_2385_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0;
    v___x_2386_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1;
    v___x_2387_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2;
    v___x_2388_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1;
    lean_inc(v_stx_2375_);
    v___x_2389_ = l_Lean_Syntax_isOfKind(v_stx_2375_, v___x_2388_);
    v___x_2390_ = 1;
    v___x_2391_ = lean_box((v___x_2389_) as usize);
    v___x_2392_ = lean_box((v___x_2390_) as usize);
    v___y_2393_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    lean_closure_set(v___y_2393_, 0, v___x_2391_);
    lean_closure_set(v___y_2393_, 1, v_stx_2375_);
    lean_closure_set(v___y_2393_, 2, v___x_2385_);
    lean_closure_set(v___y_2393_, 3, v___x_2386_);
    lean_closure_set(v___y_2393_, 4, v___x_2387_);
    lean_closure_set(v___y_2393_, 5, v___x_2392_);
    v___x_2394_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_2393_,
        v_a_2376_,
        v_a_2377_,
        v_a_2378_,
        v_a_2379_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
    );
    return v___x_2394_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(
    mut v_stx_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
    mut v_a_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(
        v_stx_2395_,
        v_a_2396_,
        v_a_2397_,
        v_a_2398_,
        v_a_2399_,
        v_a_2400_,
        v_a_2401_,
        v_a_2402_,
        v_a_2403_,
    );
    lean_dec(v_a_2403_);
    lean_dec_ref(v_a_2402_);
    lean_dec(v_a_2401_);
    lean_dec_ref(v_a_2400_);
    lean_dec(v_a_2399_);
    lean_dec_ref(v_a_2398_);
    lean_dec(v_a_2397_);
    lean_dec_ref(v_a_2396_);
    return v_res_2405_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1()
-> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2415_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1;
    v___x_2416_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1;
    v___x_2417_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2418_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2414_,
        v___x_2415_,
        v___x_2416_,
        v___x_2417_,
    );
    return v___x_2418_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(
    mut v_a_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2420_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
    return v_res_2420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
}
