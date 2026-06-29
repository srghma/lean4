// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Unfold
// Imports: Lean.Elab.Tactic.Unfold Lean.Elab.Tactic.Conv.Simp
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_replaceRef};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
    l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    l_Lean_Elab_Tactic_Conv_changeLhs, l_Lean_Elab_Tactic_Conv_getLhs___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Simp::{
    initialize_Lean_Elab_Tactic_Conv_Simp, l_Lean_Elab_Tactic_Conv_applySimpResult,
    runtime_initialize_Lean_Elab_Tactic_Conv_Simp,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_elabTermForApply___boxed;
use crate::r#gen::Lean::Elab::Tactic::Unfold::{
    initialize_Lean_Elab_Tactic_Unfold, runtime_initialize_Lean_Elab_Tactic_Unfold,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_isLetVar___redArg;
use crate::r#gen::Lean::Meta::Tactic::Unfold::l_Lean_Meta_unfold;
use crate::r#gen::Lean::Meta::Transform::l_Lean_Meta_zetaDeltaFVars;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [99, 111, 110, 118, 32, 116, 97, 99, 116, 105, 99, 32, 96, 117, 110, 102, 111, 108, 100, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32, 108, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 104, 97, 115, 32, 110, 111, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [99, 111, 110, 118, 32, 116, 97, 99, 116, 105, 99, 32, 96, 117, 110, 102, 111, 108, 100, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 103, 108, 111, 98, 97, 108, 32, 111, 114, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value) as *mut crate::leanh::LeanObject,2622230176999461939 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value) as *mut crate::leanh::LeanObject,14363068710658641377 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 85, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value) as *mut crate::leanh::LeanObject,5184926116927564615 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(
    mut v_e_437_: *mut crate::leanh::LeanObject,
    mut v___y_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: u8 = 0;
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_460_: u8 = 0;
    let mut v_unused_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_440_ = l_Lean_Expr_hasMVar(v_e_437_);
                if v___x_440_ == 0 {
                    v___x_441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_441_, 0, v_e_437_);
                    return v___x_441_;
                } else {
                    v___x_442_ = lean_st_ref_get(v___y_438_);
                    v_mctx_443_ = crate::leanh::lean_ctor_get(v___x_442_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_443_);
                    crate::leanh::lean_dec(v___x_442_);
                    v___x_444_ = l_Lean_instantiateMVarsCore(v_mctx_443_, v_e_437_);
                    v_fst_445_ = crate::leanh::lean_ctor_get(v___x_444_, 0);
                    crate::leanh::lean_inc(v_fst_445_);
                    v_snd_446_ = crate::leanh::lean_ctor_get(v___x_444_, 1);
                    crate::leanh::lean_inc(v_snd_446_);
                    crate::leanh::lean_dec_ref(v___x_444_);
                    v___x_447_ = lean_st_ref_take(v___y_438_);
                    v_cache_448_ = crate::leanh::lean_ctor_get(v___x_447_, 1);
                    v_zetaDeltaFVarIds_449_ = crate::leanh::lean_ctor_get(v___x_447_, 2);
                    v_postponed_450_ = crate::leanh::lean_ctor_get(v___x_447_, 3);
                    v_diag_451_ = crate::leanh::lean_ctor_get(v___x_447_, 4);
                    v_isSharedCheck_460_ = (!crate::leanh::lean_is_exclusive(v___x_447_)) as u8;
                    if v_isSharedCheck_460_ == 0 {
                        v_unused_461_ = crate::leanh::lean_ctor_get(v___x_447_, 0);
                        crate::leanh::lean_dec(v_unused_461_);
                        v___x_453_ = v___x_447_;
                        v_isShared_454_ = v_isSharedCheck_460_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_451_);
                        crate::leanh::lean_inc(v_postponed_450_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_449_);
                        crate::leanh::lean_inc(v_cache_448_);
                        crate::leanh::lean_dec(v___x_447_);
                        v___x_453_ = crate::leanh::lean_box(0);
                        v_isShared_454_ = v_isSharedCheck_460_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_454_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_453_, 0, v_snd_446_);
                    v___x_456_ = v___x_453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_459_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 0, v_snd_446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 1, v_cache_448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 2, v_zetaDeltaFVarIds_449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 3, v_postponed_450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 4, v_diag_451_);
                    v___x_456_ = v_reuseFailAlloc_459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_457_ = lean_st_ref_set(v___y_438_, v___x_456_);
                v___x_458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_458_, 0, v_fst_445_);
                return v___x_458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg___boxed(
    mut v_e_462_: *mut crate::leanh::LeanObject,
    mut v___y_463_: *mut crate::leanh::LeanObject,
    mut v___y_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(
        v_e_462_, v___y_463_,
    );
    crate::leanh::lean_dec(v___y_463_);
    return v_res_465_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(
    mut v_e_466_: *mut crate::leanh::LeanObject,
    mut v___y_467_: *mut crate::leanh::LeanObject,
    mut v___y_468_: *mut crate::leanh::LeanObject,
    mut v___y_469_: *mut crate::leanh::LeanObject,
    mut v___y_470_: *mut crate::leanh::LeanObject,
    mut v___y_471_: *mut crate::leanh::LeanObject,
    mut v___y_472_: *mut crate::leanh::LeanObject,
    mut v___y_473_: *mut crate::leanh::LeanObject,
    mut v___y_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(
        v_e_466_, v___y_472_,
    );
    return v___x_476_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___boxed(
    mut v_e_477_: *mut crate::leanh::LeanObject,
    mut v___y_478_: *mut crate::leanh::LeanObject,
    mut v___y_479_: *mut crate::leanh::LeanObject,
    mut v___y_480_: *mut crate::leanh::LeanObject,
    mut v___y_481_: *mut crate::leanh::LeanObject,
    mut v___y_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
    mut v___y_485_: *mut crate::leanh::LeanObject,
    mut v___y_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(
        v_e_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_,
        v___y_484_, v___y_485_,
    );
    crate::leanh::lean_dec(v___y_485_);
    crate::leanh::lean_dec_ref(v___y_484_);
    crate::leanh::lean_dec(v___y_483_);
    crate::leanh::lean_dec_ref(v___y_482_);
    crate::leanh::lean_dec(v___y_481_);
    crate::leanh::lean_dec_ref(v___y_480_);
    crate::leanh::lean_dec(v___y_479_);
    crate::leanh::lean_dec_ref(v___y_478_);
    return v_res_487_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(
    mut v_msgData_488_: *mut crate::leanh::LeanObject,
    mut v___y_489_: *mut crate::leanh::LeanObject,
    mut v___y_490_: *mut crate::leanh::LeanObject,
    mut v___y_491_: *mut crate::leanh::LeanObject,
    mut v___y_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = lean_st_ref_get(v___y_492_);
    v_env_495_ = crate::leanh::lean_ctor_get(v___x_494_, 0);
    crate::leanh::lean_inc_ref(v_env_495_);
    crate::leanh::lean_dec(v___x_494_);
    v___x_496_ = lean_st_ref_get(v___y_490_);
    v_mctx_497_ = crate::leanh::lean_ctor_get(v___x_496_, 0);
    crate::leanh::lean_inc_ref(v_mctx_497_);
    crate::leanh::lean_dec(v___x_496_);
    v_lctx_498_ = crate::leanh::lean_ctor_get(v___y_489_, 2);
    v_options_499_ = crate::leanh::lean_ctor_get(v___y_491_, 2);
    crate::leanh::lean_inc_ref(v_options_499_);
    crate::leanh::lean_inc_ref(v_lctx_498_);
    v___x_500_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_500_, 0, v_env_495_);
    crate::leanh::lean_ctor_set(v___x_500_, 1, v_mctx_497_);
    crate::leanh::lean_ctor_set(v___x_500_, 2, v_lctx_498_);
    crate::leanh::lean_ctor_set(v___x_500_, 3, v_options_499_);
    v___x_501_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_501_, 0, v___x_500_);
    crate::leanh::lean_ctor_set(v___x_501_, 1, v_msgData_488_);
    v___x_502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_502_, 0, v___x_501_);
    return v___x_502_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(
    mut v_msgData_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
    mut v___y_507_: *mut crate::leanh::LeanObject,
    mut v___y_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msgData_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
    crate::leanh::lean_dec(v___y_507_);
    crate::leanh::lean_dec_ref(v___y_506_);
    crate::leanh::lean_dec(v___y_505_);
    crate::leanh::lean_dec_ref(v___y_504_);
    return v_res_509_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(
    mut v_msg_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_516_ = crate::leanh::lean_ctor_get(v___y_513_, 5);
                v___x_517_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
                v_a_518_ = crate::leanh::lean_ctor_get(v___x_517_, 0);
                v_isSharedCheck_526_ = (!crate::leanh::lean_is_exclusive(v___x_517_)) as u8;
                if v_isSharedCheck_526_ == 0 {
                    v___x_520_ = v___x_517_;
                    v_isShared_521_ = v_isSharedCheck_526_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_518_);
                    crate::leanh::lean_dec(v___x_517_);
                    v___x_520_ = crate::leanh::lean_box(0);
                    v_isShared_521_ = v_isSharedCheck_526_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_516_);
                v___x_522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_522_, 0, v_ref_516_);
                crate::leanh::lean_ctor_set(v___x_522_, 1, v_a_518_);
                if v_isShared_521_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_520_, 1);
                    crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_522_);
                    v___x_524_ = v___x_520_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
                    v___x_524_ = v_reuseFailAlloc_525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(
    mut v_msg_527_: *mut crate::leanh::LeanObject,
    mut v___y_528_: *mut crate::leanh::LeanObject,
    mut v___y_529_: *mut crate::leanh::LeanObject,
    mut v___y_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(
        v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_,
    );
    crate::leanh::lean_dec(v___y_531_);
    crate::leanh::lean_dec_ref(v___y_530_);
    crate::leanh::lean_dec(v___y_529_);
    crate::leanh::lean_dec_ref(v___y_528_);
    return v_res_533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(
    mut v_fvarId_534_: *mut crate::leanh::LeanObject,
    mut v_____r_535_: *mut crate::leanh::LeanObject,
    mut v___y_536_: *mut crate::leanh::LeanObject,
    mut v___y_537_: *mut crate::leanh::LeanObject,
    mut v___y_538_: *mut crate::leanh::LeanObject,
    mut v___y_539_: *mut crate::leanh::LeanObject,
    mut v___y_540_: *mut crate::leanh::LeanObject,
    mut v___y_541_: *mut crate::leanh::LeanObject,
    mut v___y_542_: *mut crate::leanh::LeanObject,
    mut v___y_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_a_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_a_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_545_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_537_, v___y_540_, v___y_541_, v___y_542_, v___y_543_,
                );
                if crate::leanh::lean_obj_tag(v___x_545_) == 0 {
                    v_a_546_ = crate::leanh::lean_ctor_get(v___x_545_, 0);
                    crate::leanh::lean_inc(v_a_546_);
                    crate::leanh::lean_dec_ref_known(v___x_545_, 1);
                    v___x_547_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_a_546_, v___y_541_);
                    if crate::leanh::lean_obj_tag(v___x_547_) == 0 {
                        v_a_548_ = crate::leanh::lean_ctor_get(v___x_547_, 0);
                        crate::leanh::lean_inc(v_a_548_);
                        crate::leanh::lean_dec_ref_known(v___x_547_, 1);
                        v___x_549_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_550_ = lean_mk_empty_array_with_capacity(v___x_549_);
                        v___x_551_ = lean_array_push(v___x_550_, v_fvarId_534_);
                        v___x_552_ = l_Lean_Meta_zetaDeltaFVars(
                            v_a_548_, v___x_551_, v___y_540_, v___y_541_, v___y_542_, v___y_543_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_552_) == 0 {
                            v_a_553_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                            crate::leanh::lean_inc(v_a_553_);
                            crate::leanh::lean_dec_ref_known(v___x_552_, 1);
                            v___x_554_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_553_, v___y_536_, v___y_537_, v___y_538_, v___y_539_,
                                v___y_540_, v___y_541_, v___y_542_, v___y_543_,
                            );
                            return v___x_554_;
                        } else {
                            v_a_555_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                            v_isSharedCheck_562_ =
                                (!crate::leanh::lean_is_exclusive(v___x_552_)) as u8;
                            if v_isSharedCheck_562_ == 0 {
                                v___x_557_ = v___x_552_;
                                v_isShared_558_ = v_isSharedCheck_562_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_555_);
                                crate::leanh::lean_dec(v___x_552_);
                                v___x_557_ = crate::leanh::lean_box(0);
                                v_isShared_558_ = v_isSharedCheck_562_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_534_);
                        v_a_563_ = crate::leanh::lean_ctor_get(v___x_547_, 0);
                        v_isSharedCheck_570_ = (!crate::leanh::lean_is_exclusive(v___x_547_)) as u8;
                        if v_isSharedCheck_570_ == 0 {
                            v___x_565_ = v___x_547_;
                            v_isShared_566_ = v_isSharedCheck_570_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_563_);
                            crate::leanh::lean_dec(v___x_547_);
                            v___x_565_ = crate::leanh::lean_box(0);
                            v_isShared_566_ = v_isSharedCheck_570_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_534_);
                    v_a_571_ = crate::leanh::lean_ctor_get(v___x_545_, 0);
                    v_isSharedCheck_578_ = (!crate::leanh::lean_is_exclusive(v___x_545_)) as u8;
                    if v_isSharedCheck_578_ == 0 {
                        v___x_573_ = v___x_545_;
                        v_isShared_574_ = v_isSharedCheck_578_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_571_);
                        crate::leanh::lean_dec(v___x_545_);
                        v___x_573_ = crate::leanh::lean_box(0);
                        v_isShared_574_ = v_isSharedCheck_578_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_558_ == 0 {
                    v___x_560_ = v___x_557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_560_;
            }
            3 => {
                if v_isShared_566_ == 0 {
                    v___x_568_ = v___x_565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
                    v___x_568_ = v_reuseFailAlloc_569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_568_;
            }
            5 => {
                if v_isShared_574_ == 0 {
                    v___x_576_ = v___x_573_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed(
    mut v_fvarId_579_: *mut crate::leanh::LeanObject,
    mut v_____r_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
    mut v___y_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_579_, v_____r_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
    crate::leanh::lean_dec(v___y_588_);
    crate::leanh::lean_dec_ref(v___y_587_);
    crate::leanh::lean_dec(v___y_586_);
    crate::leanh::lean_dec_ref(v___y_585_);
    crate::leanh::lean_dec(v___y_584_);
    crate::leanh::lean_dec_ref(v___y_583_);
    crate::leanh::lean_dec(v___y_582_);
    crate::leanh::lean_dec_ref(v___y_581_);
    return v_res_590_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0;
    v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2;
    v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
    return v___x_596_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4;
    v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
    return v___x_599_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6;
    v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
    return v___x_602_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(
    mut v_as_603_: *mut crate::leanh::LeanObject,
    mut v_sz_604_: usize,
    mut v_i_605_: usize,
    mut v_b_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
    mut v___y_612_: *mut crate::leanh::LeanObject,
    mut v___y_613_: *mut crate::leanh::LeanObject,
    mut v___y_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_630_: u8 = 0;
    let mut v_cancelTk_x3f_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_632_: u8 = 0;
    let mut v_inheritedTraceOptions_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: usize = 0;
    let mut v___x_646_: usize = 0;
    let mut v_declName_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_657_: u8 = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_a_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_665_: u8 = 0;
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_669_: u8 = 0;
    let mut v_fvarId_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: u8 = 0;
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_616_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
                if v___x_616_ == 0 {
                    v___x_617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_617_, 0, v_b_606_);
                    return v___x_617_;
                } else {
                    v_fileName_618_ = crate::leanh::lean_ctor_get(v___y_613_, 0);
                    v_fileMap_619_ = crate::leanh::lean_ctor_get(v___y_613_, 1);
                    v_options_620_ = crate::leanh::lean_ctor_get(v___y_613_, 2);
                    v_currRecDepth_621_ = crate::leanh::lean_ctor_get(v___y_613_, 3);
                    v_maxRecDepth_622_ = crate::leanh::lean_ctor_get(v___y_613_, 4);
                    v_ref_623_ = crate::leanh::lean_ctor_get(v___y_613_, 5);
                    v_currNamespace_624_ = crate::leanh::lean_ctor_get(v___y_613_, 6);
                    v_openDecls_625_ = crate::leanh::lean_ctor_get(v___y_613_, 7);
                    v_initHeartbeats_626_ = crate::leanh::lean_ctor_get(v___y_613_, 8);
                    v_maxHeartbeats_627_ = crate::leanh::lean_ctor_get(v___y_613_, 9);
                    v_quotContext_628_ = crate::leanh::lean_ctor_get(v___y_613_, 10);
                    v_currMacroScope_629_ = crate::leanh::lean_ctor_get(v___y_613_, 11);
                    v_diag_630_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_613_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_631_ = crate::leanh::lean_ctor_get(v___y_613_, 12);
                    v_suppressElabErrors_632_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_613_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_633_ = crate::leanh::lean_ctor_get(v___y_613_, 13);
                    v_a_634_ = lean_array_uget_borrowed(v_as_603_, v_i_605_);
                    v___x_635_ = 0;
                    v___x_636_ = crate::leanh::lean_box((v___x_635_) as usize);
                    crate::leanh::lean_inc(v_a_634_);
                    v___x_637_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_elabTermForApply___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_637_, 0, v_a_634_);
                    crate::leanh::lean_closure_set(v___x_637_, 1, v___x_636_);
                    v_ref_638_ = l_Lean_replaceRef(v_a_634_, v_ref_623_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_633_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_631_);
                    crate::leanh::lean_inc(v_currMacroScope_629_);
                    crate::leanh::lean_inc(v_quotContext_628_);
                    crate::leanh::lean_inc(v_maxHeartbeats_627_);
                    crate::leanh::lean_inc(v_initHeartbeats_626_);
                    crate::leanh::lean_inc(v_openDecls_625_);
                    crate::leanh::lean_inc(v_currNamespace_624_);
                    crate::leanh::lean_inc(v_maxRecDepth_622_);
                    crate::leanh::lean_inc(v_currRecDepth_621_);
                    crate::leanh::lean_inc_ref(v_options_620_);
                    crate::leanh::lean_inc_ref(v_fileMap_619_);
                    crate::leanh::lean_inc_ref(v_fileName_618_);
                    v___x_639_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_639_, 0, v_fileName_618_);
                    crate::leanh::lean_ctor_set(v___x_639_, 1, v_fileMap_619_);
                    crate::leanh::lean_ctor_set(v___x_639_, 2, v_options_620_);
                    crate::leanh::lean_ctor_set(v___x_639_, 3, v_currRecDepth_621_);
                    crate::leanh::lean_ctor_set(v___x_639_, 4, v_maxRecDepth_622_);
                    crate::leanh::lean_ctor_set(v___x_639_, 5, v_ref_638_);
                    crate::leanh::lean_ctor_set(v___x_639_, 6, v_currNamespace_624_);
                    crate::leanh::lean_ctor_set(v___x_639_, 7, v_openDecls_625_);
                    crate::leanh::lean_ctor_set(v___x_639_, 8, v_initHeartbeats_626_);
                    crate::leanh::lean_ctor_set(v___x_639_, 9, v_maxHeartbeats_627_);
                    crate::leanh::lean_ctor_set(v___x_639_, 10, v_quotContext_628_);
                    crate::leanh::lean_ctor_set(v___x_639_, 11, v_currMacroScope_629_);
                    crate::leanh::lean_ctor_set(v___x_639_, 12, v_cancelTk_x3f_631_);
                    crate::leanh::lean_ctor_set(v___x_639_, 13, v_inheritedTraceOptions_633_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_639_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_630_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_639_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_632_,
                    );
                    v___x_640_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                        v___x_637_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_,
                        v___y_612_, v___x_639_, v___y_614_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_640_) == 0 {
                        v_a_641_ = crate::leanh::lean_ctor_get(v___x_640_, 0);
                        crate::leanh::lean_inc(v_a_641_);
                        crate::leanh::lean_dec_ref_known(v___x_640_, 1);
                        v___x_642_ = crate::leanh::lean_box(0);
                        match crate::leanh::lean_obj_tag(v_a_641_) {
                            4 => {
                                v_declName_648_ = crate::leanh::lean_ctor_get(v_a_641_, 0);
                                crate::leanh::lean_inc(v_declName_648_);
                                crate::leanh::lean_dec_ref_known(v_a_641_, 2);
                                v___x_649_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                                    v___y_608_, v___y_611_, v___y_612_, v___x_639_, v___y_614_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_649_) == 0 {
                                    v_a_650_ = crate::leanh::lean_ctor_get(v___x_649_, 0);
                                    crate::leanh::lean_inc(v_a_650_);
                                    crate::leanh::lean_dec_ref_known(v___x_649_, 1);
                                    v___x_651_ = l_Lean_Meta_unfold(
                                        v_a_650_,
                                        v_declName_648_,
                                        v___y_611_,
                                        v___y_612_,
                                        v___x_639_,
                                        v___y_614_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_651_) == 0 {
                                        v_a_652_ = crate::leanh::lean_ctor_get(v___x_651_, 0);
                                        crate::leanh::lean_inc(v_a_652_);
                                        crate::leanh::lean_dec_ref_known(v___x_651_, 1);
                                        v___x_653_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                                            v_a_652_, v___y_607_, v___y_608_, v___y_609_,
                                            v___y_610_, v___y_611_, v___y_612_, v___x_639_,
                                            v___y_614_,
                                        );
                                        crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                        v___y_644_ = v___x_653_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                        v_a_654_ = crate::leanh::lean_ctor_get(v___x_651_, 0);
                                        v_isSharedCheck_661_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_651_)) as u8;
                                        if v_isSharedCheck_661_ == 0 {
                                            v___x_656_ = v___x_651_;
                                            v_isShared_657_ = v_isSharedCheck_661_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_654_);
                                            crate::leanh::lean_dec(v___x_651_);
                                            v___x_656_ = crate::leanh::lean_box(0);
                                            v_isShared_657_ = v_isSharedCheck_661_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_declName_648_);
                                    crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                    v_a_662_ = crate::leanh::lean_ctor_get(v___x_649_, 0);
                                    v_isSharedCheck_669_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_649_)) as u8;
                                    if v_isSharedCheck_669_ == 0 {
                                        v___x_664_ = v___x_649_;
                                        v_isShared_665_ = v_isSharedCheck_669_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_662_);
                                        crate::leanh::lean_dec(v___x_649_);
                                        v___x_664_ = crate::leanh::lean_box(0);
                                        v_isShared_665_ = v_isSharedCheck_669_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                            1 => {
                                v_fvarId_670_ = crate::leanh::lean_ctor_get(v_a_641_, 0);
                                crate::leanh::lean_inc_n(v_fvarId_670_, 2);
                                v___x_671_ = l_Lean_FVarId_isLetVar___redArg(
                                    v_fvarId_670_,
                                    v___x_635_,
                                    v___y_611_,
                                    v___x_639_,
                                    v___y_614_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_671_) == 0 {
                                    v_a_672_ = crate::leanh::lean_ctor_get(v___x_671_, 0);
                                    crate::leanh::lean_inc(v_a_672_);
                                    crate::leanh::lean_dec_ref_known(v___x_671_, 1);
                                    v___x_673_ = (crate::leanh::lean_unbox(v_a_672_) as u8);
                                    crate::leanh::lean_dec(v_a_672_);
                                    if v___x_673_ == 0 {
                                        v___x_674_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1);
                                        v___x_675_ = l_Lean_MessageData_ofExpr(v_a_641_);
                                        v___x_676_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_674_);
                                        crate::leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                                        v___x_677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3);
                                        v___x_678_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_678_, 0, v___x_676_);
                                        crate::leanh::lean_ctor_set(v___x_678_, 1, v___x_677_);
                                        v___x_679_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_678_, v___y_611_, v___y_612_, v___x_639_, v___y_614_);
                                        if crate::leanh::lean_obj_tag(v___x_679_) == 0 {
                                            v_a_680_ = crate::leanh::lean_ctor_get(v___x_679_, 0);
                                            crate::leanh::lean_inc(v_a_680_);
                                            crate::leanh::lean_dec_ref_known(v___x_679_, 1);
                                            v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_670_, v_a_680_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___x_639_, v___y_614_);
                                            crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                            v___y_644_ = v___x_681_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_fvarId_670_);
                                            crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                            v___y_644_ = v___x_679_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_a_641_, 1);
                                        v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_670_, v___x_642_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___x_639_, v___y_614_);
                                        crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                        v___y_644_ = v___x_682_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_a_641_, 1);
                                    crate::leanh::lean_dec(v_fvarId_670_);
                                    crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                    v_a_683_ = crate::leanh::lean_ctor_get(v___x_671_, 0);
                                    v_isSharedCheck_690_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_671_)) as u8;
                                    if v_isSharedCheck_690_ == 0 {
                                        v___x_685_ = v___x_671_;
                                        v_isShared_686_ = v_isSharedCheck_690_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_683_);
                                        crate::leanh::lean_dec(v___x_671_);
                                        v___x_685_ = crate::leanh::lean_box(0);
                                        v_isShared_686_ = v_isSharedCheck_690_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v___x_691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5);
                                v___x_692_ = l_Lean_MessageData_ofExpr(v_a_641_);
                                v___x_693_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_693_, 0, v___x_691_);
                                crate::leanh::lean_ctor_set(v___x_693_, 1, v___x_692_);
                                v___x_694_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7);
                                v___x_695_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_695_, 0, v___x_693_);
                                crate::leanh::lean_ctor_set(v___x_695_, 1, v___x_694_);
                                v___x_696_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_695_, v___y_611_, v___y_612_, v___x_639_, v___y_614_);
                                crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                                v___y_644_ = v___x_696_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_639_, 14);
                        v_a_697_ = crate::leanh::lean_ctor_get(v___x_640_, 0);
                        v_isSharedCheck_704_ = (!crate::leanh::lean_is_exclusive(v___x_640_)) as u8;
                        if v_isSharedCheck_704_ == 0 {
                            v___x_699_ = v___x_640_;
                            v_isShared_700_ = v_isSharedCheck_704_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_697_);
                            crate::leanh::lean_dec(v___x_640_);
                            v___x_699_ = crate::leanh::lean_box(0);
                            v_isShared_700_ = v_isSharedCheck_704_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_644_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_644_, 1);
                    v___x_645_ = 1usize;
                    v___x_646_ = lean_usize_add(v_i_605_, v___x_645_);
                    v_i_605_ = v___x_646_;
                    v_b_606_ = v___x_642_;
                    state = 0;
                    continue;
                } else {
                    return v___y_644_;
                }
            }
            2 => {
                if v_isShared_657_ == 0 {
                    v___x_659_ = v___x_656_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
                    v___x_659_ = v_reuseFailAlloc_660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_659_;
            }
            4 => {
                if v_isShared_665_ == 0 {
                    v___x_667_ = v___x_664_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
                    v___x_667_ = v_reuseFailAlloc_668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_667_;
            }
            6 => {
                if v_isShared_686_ == 0 {
                    v___x_688_ = v___x_685_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
                    v___x_688_ = v_reuseFailAlloc_689_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_688_;
            }
            8 => {
                if v_isShared_700_ == 0 {
                    v___x_702_ = v___x_699_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
                    v___x_702_ = v_reuseFailAlloc_703_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___boxed(
    mut v_as_705_: *mut crate::leanh::LeanObject,
    mut v_sz_706_: *mut crate::leanh::LeanObject,
    mut v_i_707_: *mut crate::leanh::LeanObject,
    mut v_b_708_: *mut crate::leanh::LeanObject,
    mut v___y_709_: *mut crate::leanh::LeanObject,
    mut v___y_710_: *mut crate::leanh::LeanObject,
    mut v___y_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
    mut v___y_715_: *mut crate::leanh::LeanObject,
    mut v___y_716_: *mut crate::leanh::LeanObject,
    mut v___y_717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_718_: usize = 0;
    let mut v_i_boxed_719_: usize = 0;
    let mut v_res_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_718_ = crate::leanh::lean_unbox_usize(v_sz_706_);
    crate::leanh::lean_dec(v_sz_706_);
    v_i_boxed_719_ = crate::leanh::lean_unbox_usize(v_i_707_);
    crate::leanh::lean_dec(v_i_707_);
    v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v_as_705_, v_sz_boxed_718_, v_i_boxed_719_, v_b_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
    crate::leanh::lean_dec(v___y_716_);
    crate::leanh::lean_dec_ref(v___y_715_);
    crate::leanh::lean_dec(v___y_714_);
    crate::leanh::lean_dec_ref(v___y_713_);
    crate::leanh::lean_dec(v___y_712_);
    crate::leanh::lean_dec_ref(v___y_711_);
    crate::leanh::lean_dec(v___y_710_);
    crate::leanh::lean_dec_ref(v___y_709_);
    crate::leanh::lean_dec_ref(v_as_705_);
    return v_res_720_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(
    mut v___x_721_: *mut crate::leanh::LeanObject,
    mut v_sz_722_: usize,
    mut v___x_723_: usize,
    mut v___x_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
    mut v___y_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_737_: u8 = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v___x_721_, v_sz_722_, v___x_723_, v___x_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
                if crate::leanh::lean_obj_tag(v___x_734_) == 0 {
                    v_isSharedCheck_741_ = (!crate::leanh::lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_741_ == 0 {
                        v_unused_742_ = crate::leanh::lean_ctor_get(v___x_734_, 0);
                        crate::leanh::lean_dec(v_unused_742_);
                        v___x_736_ = v___x_734_;
                        v_isShared_737_ = v_isSharedCheck_741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_734_);
                        v___x_736_ = crate::leanh::lean_box(0);
                        v_isShared_737_ = v_isSharedCheck_741_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_734_;
                }
            }
            1 => {
                if v_isShared_737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_736_, 0, v___x_724_);
                    v___x_739_ = v___x_736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_724_);
                    v___x_739_ = v_reuseFailAlloc_740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed(
    mut v___x_743_: *mut crate::leanh::LeanObject,
    mut v_sz_744_: *mut crate::leanh::LeanObject,
    mut v___x_745_: *mut crate::leanh::LeanObject,
    mut v___x_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_756_: usize = 0;
    let mut v___x_7781__boxed_757_: usize = 0;
    let mut v_res_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_756_ = crate::leanh::lean_unbox_usize(v_sz_744_);
    crate::leanh::lean_dec(v_sz_744_);
    v___x_7781__boxed_757_ = crate::leanh::lean_unbox_usize(v___x_745_);
    crate::leanh::lean_dec(v___x_745_);
    v_res_758_ = l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(
        v___x_743_,
        v_sz_boxed_756_,
        v___x_7781__boxed_757_,
        v___x_746_,
        v___y_747_,
        v___y_748_,
        v___y_749_,
        v___y_750_,
        v___y_751_,
        v___y_752_,
        v___y_753_,
        v___y_754_,
    );
    crate::leanh::lean_dec(v___y_754_);
    crate::leanh::lean_dec_ref(v___y_753_);
    crate::leanh::lean_dec(v___y_752_);
    crate::leanh::lean_dec_ref(v___y_751_);
    crate::leanh::lean_dec(v___y_750_);
    crate::leanh::lean_dec_ref(v___y_749_);
    crate::leanh::lean_dec(v___y_748_);
    crate::leanh::lean_dec_ref(v___y_747_);
    crate::leanh::lean_dec_ref(v___x_743_);
    return v_res_758_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalUnfold(
    mut v_stx_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
    mut v_a_765_: *mut crate::leanh::LeanObject,
    mut v_a_766_: *mut crate::leanh::LeanObject,
    mut v_a_767_: *mut crate::leanh::LeanObject,
    mut v_a_768_: *mut crate::leanh::LeanObject,
    mut v_a_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_775_: usize = 0;
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_772_ = l_Lean_Syntax_getArg(v_stx_761_, v___x_771_);
    v___x_773_ = l_Lean_Syntax_getArgs(v___x_772_);
    crate::leanh::lean_dec(v___x_772_);
    v___x_774_ = crate::leanh::lean_box(0);
    v_sz_775_ = lean_array_size(v___x_773_);
    v___x_776_ = crate::leanh::lean_box_usize(v_sz_775_);
    v___x_777_ = l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1;
    v___f_778_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    crate::leanh::lean_closure_set(v___f_778_, 0, v___x_773_);
    crate::leanh::lean_closure_set(v___f_778_, 1, v___x_776_);
    crate::leanh::lean_closure_set(v___f_778_, 2, v___x_777_);
    crate::leanh::lean_closure_set(v___f_778_, 3, v___x_774_);
    v___x_779_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_778_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_,
    );
    return v___x_779_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(
    mut v_stx_780_: *mut crate::leanh::LeanObject,
    mut v_a_781_: *mut crate::leanh::LeanObject,
    mut v_a_782_: *mut crate::leanh::LeanObject,
    mut v_a_783_: *mut crate::leanh::LeanObject,
    mut v_a_784_: *mut crate::leanh::LeanObject,
    mut v_a_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
    mut v_a_788_: *mut crate::leanh::LeanObject,
    mut v_a_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Elab_Tactic_Conv_evalUnfold(
        v_stx_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_,
    );
    crate::leanh::lean_dec(v_a_788_);
    crate::leanh::lean_dec_ref(v_a_787_);
    crate::leanh::lean_dec(v_a_786_);
    crate::leanh::lean_dec_ref(v_a_785_);
    crate::leanh::lean_dec(v_a_784_);
    crate::leanh::lean_dec_ref(v_a_783_);
    crate::leanh::lean_dec(v_a_782_);
    crate::leanh::lean_dec_ref(v_a_781_);
    crate::leanh::lean_dec(v_stx_780_);
    return v_res_790_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(
    mut v_00_u03b1_791_: *mut crate::leanh::LeanObject,
    mut v_msg_792_: *mut crate::leanh::LeanObject,
    mut v___y_793_: *mut crate::leanh::LeanObject,
    mut v___y_794_: *mut crate::leanh::LeanObject,
    mut v___y_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
    mut v___y_798_: *mut crate::leanh::LeanObject,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(
        v_msg_792_, v___y_797_, v___y_798_, v___y_799_, v___y_800_,
    );
    return v___x_802_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___boxed(
    mut v_00_u03b1_803_: *mut crate::leanh::LeanObject,
    mut v_msg_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(
        v_00_u03b1_803_,
        v_msg_804_,
        v___y_805_,
        v___y_806_,
        v___y_807_,
        v___y_808_,
        v___y_809_,
        v___y_810_,
        v___y_811_,
        v___y_812_,
    );
    crate::leanh::lean_dec(v___y_812_);
    crate::leanh::lean_dec_ref(v___y_811_);
    crate::leanh::lean_dec(v___y_810_);
    crate::leanh::lean_dec_ref(v___y_809_);
    crate::leanh::lean_dec(v___y_808_);
    crate::leanh::lean_dec_ref(v___y_807_);
    crate::leanh::lean_dec(v___y_806_);
    crate::leanh::lean_dec_ref(v___y_805_);
    return v_res_814_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_836_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5;
    v___x_837_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8;
    v___x_838_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalUnfold___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_839_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_835_, v___x_836_, v___x_837_, v___x_838_,
    );
    return v___x_839_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___boxed(
    mut v_a_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_841_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
    return v_res_841_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8;
    v___x_869_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6;
    v___x_870_ = l_Lean_addBuiltinDeclarationRanges(v___x_868_, v___x_869_);
    return v___x_870_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___boxed(
    mut v_a_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
    return v_res_872_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Unfold(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Unfold(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Unfold(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
}
