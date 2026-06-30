// Lean compiler output
// Module: Lean.Server.Completion.SyntheticCompletion
// Imports: Lean.Server.InfoUtils Lean.Server.Completion.CompletionUtils
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_utf8_at_end, lean_string_utf8_get, lean_string_utf8_next, lean_uint32_dec_eq,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_zipIdx___redArg,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_head_x3f___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getTrailingSize, l_Lean_Syntax_getTrailingTailPos_x3f, l_Lean_Syntax_hasArgs,
    l_Lean_Syntax_isAtom, l_Lean_Syntax_isToken, l_Lean_TSyntax_getId,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_toList___redArg;
use crate::r#gen::Lean::Data::Position::{l_Lean_FileMap_lineStart, l_Lean_FileMap_toPosition};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_Info_updateContext_x3f, l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_getAppFn, l_Lean_instInhabitedExpr};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalContext_empty, lean_local_ctx_is_empty};
use crate::r#gen::Lean::Server::Completion::CompletionUtils::{
    initialize_Lean_Server_Completion_CompletionUtils,
    runtime_initialize_Lean_Server_Completion_CompletionUtils,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, l_Lean_Elab_Info_isSmaller, l_Lean_Elab_Info_lctx,
    l_Lean_Elab_Info_occursInOrOnBoundary, l_Lean_Elab_Info_pos_x3f, l_Lean_Elab_Info_stx,
    l_Lean_Elab_Info_tailPos_x3f, l_Lean_Elab_InfoTree_smallestInfo_x3f,
    runtime_initialize_Lean_Server_InfoUtils,
};
use crate::r#gen::Lean::Structure::l_Lean_isStructure;
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_contains, l_Lean_Syntax_findStack_x3f, l_Lean_Syntax_getRange_x3f,
};
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 116, 101, 120, 116, 45, 102, 114, 101, 101, 32, 105, 110, 102, 111, 32, 116, 114, 101, 101, 32, 110, 111, 100, 101, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value: leanh::LeanStringObject<62> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 110, 102, 111, 84, 114, 101, 101, 46, 118, 105, 115, 105, 116, 77, 46, 103, 111, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 73, 110, 102, 111, 85, 116, 105, 108, 115, 0]};
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 0]};
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value) as *mut leanh::LeanObject;
static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__5_value) as *mut leanh::LeanObject,17147433139942273511 as *mut leanh::LeanObject] };
static mut l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
static l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject,14183307858573822893 as *mut leanh::LeanObject] };
static mut l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__1_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__3_value) as *mut leanh::LeanObject,10468396288943149198 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__0_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 8 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__4_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__0_value) as *mut leanh::LeanObject,5018042693327868416 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Server_Completion_findSyntheticCompletions___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_Completion_findSyntheticCompletions___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Completion_findSyntheticCompletions___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(
    mut v_gt_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_b_1256_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_a_1255_) == 0 {
        let mut v___x_1257_: u8 = 0;
        leanh::lean_dec(v_b_1256_);
        leanh::lean_dec_ref(v_gt_1254_);
        v___x_1257_ = 0;
        return v___x_1257_;
    } else {
        if leanh::lean_obj_tag(v_b_1256_) == 0 {
            let mut v___x_1258_: u8 = 0;
            leanh::lean_dec_ref_known(v_a_1255_, 1);
            leanh::lean_dec_ref(v_gt_1254_);
            v___x_1258_ = 1;
            return v___x_1258_;
        } else {
            let mut v_val_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: u8 = 0;
            v_val_1259_ = leanh::lean_ctor_get(v_a_1255_, 0);
            leanh::lean_inc(v_val_1259_);
            leanh::lean_dec_ref_known(v_a_1255_, 1);
            v_val_1260_ = leanh::lean_ctor_get(v_b_1256_, 0);
            leanh::lean_inc(v_val_1260_);
            leanh::lean_dec_ref_known(v_b_1256_, 1);
            v___x_1261_ = leanh::lean_apply_2(v_gt_1254_, v_val_1259_, v_val_1260_);
            v___x_1262_ = (leanh::lean_unbox(v___x_1261_) as u8);
            return v___x_1262_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg___boxed(
    mut v_gt_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
    mut v_b_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1266_: u8 = 0;
    let mut v_r_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_1263_, v_a_1264_, v_b_1265_);
    v_r_1267_ = leanh::lean_box((v_res_1266_) as usize);
    return v_r_1267_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(
    mut v_00_u03b1_1268_: *mut leanh::LeanObject,
    mut v_gt_1269_: *mut leanh::LeanObject,
    mut v_a_1270_: *mut leanh::LeanObject,
    mut v_b_1271_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1272_: u8 = 0;
    v___x_1272_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_1269_, v_a_1270_, v_b_1271_);
    return v___x_1272_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___boxed(
    mut v_00_u03b1_1273_: *mut leanh::LeanObject,
    mut v_gt_1274_: *mut leanh::LeanObject,
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_b_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1277_: u8 = 0;
    let mut v_r_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter(v_00_u03b1_1273_, v_gt_1274_, v_a_1275_, v_b_1276_);
    v_r_1278_ = leanh::lean_box((v_res_1277_) as usize);
    return v_r_1278_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(
    mut v_a_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___y_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1279_) == 0 {
                    v___x_1281_ = l_List_reverse___redArg(v_a_1280_);
                    return v___x_1281_;
                } else {
                    v_head_1282_ = leanh::lean_ctor_get(v_a_1279_, 0);
                    v_tail_1283_ = leanh::lean_ctor_get(v_a_1279_, 1);
                    v_isSharedCheck_1295_ = (!leanh::lean_is_exclusive(v_a_1279_)) as u8;
                    if v_isSharedCheck_1295_ == 0 {
                        v___x_1285_ = v_a_1279_;
                        v_isShared_1286_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1283_);
                        leanh::lean_inc(v_head_1282_);
                        leanh::lean_dec(v_a_1279_);
                        v___x_1285_ = leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_head_1282_) == 0 {
                    v___x_1293_ = leanh::lean_box(0);
                    v___y_1288_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_val_1294_ = leanh::lean_ctor_get(v_head_1282_, 0);
                    leanh::lean_inc(v_val_1294_);
                    leanh::lean_dec_ref_known(v_head_1282_, 1);
                    v___y_1288_ = v_val_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1286_ == 0 {
                    leanh::lean_ctor_set(v___x_1285_, 1, v_a_1280_);
                    leanh::lean_ctor_set(v___x_1285_, 0, v___y_1288_);
                    v___x_1290_ = v___x_1285_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___y_1288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_a_1280_);
                    v___x_1290_ = v_reuseFailAlloc_1292_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1279_ = v_tail_1283_;
                v_a_1280_ = v___x_1290_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(
    mut v_gt_1296_: *mut leanh::LeanObject,
    mut v_x_1297_: *mut leanh::LeanObject,
    mut v_x_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1298_) == 0 {
                    leanh::lean_dec_ref(v_gt_1296_);
                    return v_x_1297_;
                } else {
                    v_head_1299_ = leanh::lean_ctor_get(v_x_1298_, 0);
                    leanh::lean_inc_n(v_head_1299_, 2);
                    v_tail_1300_ = leanh::lean_ctor_get(v_x_1298_, 1);
                    leanh::lean_inc(v_tail_1300_);
                    leanh::lean_dec_ref_known(v_x_1298_, 2);
                    leanh::lean_inc(v_x_1297_);
                    leanh::lean_inc_ref(v_gt_1296_);
                    v___x_1301_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_1296_, v_x_1297_, v_head_1299_);
                    if v___x_1301_ == 0 {
                        leanh::lean_dec(v_x_1297_);
                        v_x_1297_ = v_head_1299_;
                        v_x_1298_ = v_tail_1300_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1299_);
                        v_x_1298_ = v_tail_1300_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(
    mut v_gt_1304_: *mut leanh::LeanObject,
    mut v_f_1305_: *mut leanh::LeanObject,
    mut v_ctx_1306_: *mut leanh::LeanObject,
    mut v_info_1307_: *mut leanh::LeanObject,
    mut v_cs_1308_: *mut leanh::LeanObject,
    mut v_childValues_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bestChildValue_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = leanh::lean_box(0);
    v___x_1311_ = leanh::lean_box(0);
    v___x_1312_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_childValues_1309_, v___x_1311_);
    leanh::lean_inc_ref(v_gt_1304_);
    v_bestChildValue_1313_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_1304_, v___x_1310_, v___x_1312_);
    v___x_1314_ = leanh::lean_apply_3(v_f_1305_, v_ctx_1306_, v_info_1307_, v_cs_1308_);
    if leanh::lean_obj_tag(v___x_1314_) == 1 {
        let mut v___x_1315_: u8 = 0;
        leanh::lean_inc(v_bestChildValue_1313_);
        leanh::lean_inc_ref(v___x_1314_);
        v___x_1315_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_isBetter___redArg(v_gt_1304_, v___x_1314_, v_bestChildValue_1313_);
        if v___x_1315_ == 0 {
            leanh::lean_dec_ref_known(v___x_1314_, 1);
            return v_bestChildValue_1313_;
        } else {
            leanh::lean_dec(v_bestChildValue_1313_);
            return v___x_1314_;
        }
    } else {
        leanh::lean_dec(v___x_1314_);
        leanh::lean_dec_ref(v_gt_1304_);
        return v_bestChildValue_1313_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose(
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_gt_1317_: *mut leanh::LeanObject,
    mut v_f_1318_: *mut leanh::LeanObject,
    mut v_ctx_1319_: *mut leanh::LeanObject,
    mut v_info_1320_: *mut leanh::LeanObject,
    mut v_cs_1321_: *mut leanh::LeanObject,
    mut v_childValues_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose___redArg(v_gt_1317_, v_f_1318_, v_ctx_1319_, v_info_1320_, v_cs_1321_, v_childValues_1322_);
    return v___x_1323_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0(
    mut v_00_u03b1_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_List_mapTR_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__0___redArg(v_a_1325_, v_a_1326_);
    return v___x_1327_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1(
    mut v_00_u03b1_1328_: *mut leanh::LeanObject,
    mut v_gt_1329_: *mut leanh::LeanObject,
    mut v_x_1330_: *mut leanh::LeanObject,
    mut v_x_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_List_foldl___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose_spec__1___redArg(v_gt_1329_, v_x_1330_, v_x_1331_);
    return v___x_1332_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(
    mut v_x_1333_: *mut leanh::LeanObject,
    mut v_x_1334_: *mut leanh::LeanObject,
    mut v_x_1335_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1336_: u8 = 0;
    v___x_1336_ = 1;
    return v___x_1336_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0___boxed(
    mut v_x_1337_: *mut leanh::LeanObject,
    mut v_x_1338_: *mut leanh::LeanObject,
    mut v_x_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: u8 = 0;
    let mut v_r_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___lam__0(v_x_1337_, v_x_1338_, v_x_1339_);
    leanh::lean_dec_ref(v_x_1339_);
    leanh::lean_dec_ref(v_x_1338_);
    leanh::lean_dec_ref(v_x_1337_);
    v_r_1341_ = leanh::lean_box((v_res_1340_) as usize);
    return v_r_1341_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(
    mut v_msg_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1350_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0;
    v___f_1351_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1;
    v___f_1352_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2;
    v___f_1353_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3;
    v___f_1354_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4;
    v___f_1355_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5;
    v___f_1356_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6;
    v___x_1357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1357_, 0, v___f_1350_);
    leanh::lean_ctor_set(v___x_1357_, 1, v___f_1351_);
    v___x_1358_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    leanh::lean_ctor_set(v___x_1358_, 1, v___f_1352_);
    leanh::lean_ctor_set(v___x_1358_, 2, v___f_1353_);
    leanh::lean_ctor_set(v___x_1358_, 3, v___f_1354_);
    leanh::lean_ctor_set(v___x_1358_, 4, v___f_1355_);
    v___x_1359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1359_, 0, v___x_1358_);
    leanh::lean_ctor_set(v___x_1359_, 1, v___f_1356_);
    v___x_1360_ = leanh::lean_box(0);
    v___x_1361_ = l_instInhabitedOfMonad___redArg(v___x_1359_, v___x_1360_);
    v___x_1362_ = lean_panic_fn_borrowed(v___x_1361_, v_msg_1349_);
    leanh::lean_dec(v___x_1361_);
    return v___x_1362_;
}
pub unsafe fn _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__2;
    v___x_1367_ = leanh::lean_unsigned_to_nat(21);
    v___x_1368_ = leanh::lean_unsigned_to_nat(65);
    v___x_1369_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__1;
    v___x_1370_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__0;
    v___x_1371_ = l_mkPanicMessageWithDecl(
        v___x_1370_,
        v___x_1369_,
        v___x_1368_,
        v___x_1367_,
        v___x_1366_,
    );
    return v___x_1371_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(
    mut v_preNode_1372_: *mut leanh::LeanObject,
    mut v_postNode_1373_: *mut leanh::LeanObject,
    mut v_x_1374_: *mut leanh::LeanObject,
    mut v_x_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_unused_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1375_) {
                0 => {
                    v_i_1376_ = leanh::lean_ctor_get(v_x_1375_, 0);
                    leanh::lean_inc_ref(v_i_1376_);
                    v_t_1377_ = leanh::lean_ctor_get(v_x_1375_, 1);
                    leanh::lean_inc_ref(v_t_1377_);
                    leanh::lean_dec_ref_known(v_x_1375_, 2);
                    v___x_1378_ =
                        l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1376_, v_x_1374_);
                    v_x_1374_ = v___x_1378_;
                    v_x_1375_ = v_t_1377_;
                    state = 0;
                    continue;
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_1374_) == 0 {
                        leanh::lean_dec_ref_known(v_x_1375_, 2);
                        leanh::lean_dec(v_postNode_1373_);
                        leanh::lean_dec_ref(v_preNode_1372_);
                        v___x_1380_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3_once), _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg___closed__3);
                        v___x_1381_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v___x_1380_);
                        return v___x_1381_;
                    } else {
                        v_i_1382_ = leanh::lean_ctor_get(v_x_1375_, 0);
                        leanh::lean_inc_ref_n(v_i_1382_, 2);
                        v_children_1383_ = leanh::lean_ctor_get(v_x_1375_, 1);
                        leanh::lean_inc_ref_n(v_children_1383_, 2);
                        leanh::lean_dec_ref_known(v_x_1375_, 2);
                        v_val_1384_ = leanh::lean_ctor_get(v_x_1374_, 0);
                        leanh::lean_inc_n(v_val_1384_, 2);
                        leanh::lean_inc_ref(v_preNode_1372_);
                        v___x_1385_ = leanh::lean_apply_3(
                            v_preNode_1372_,
                            v_val_1384_,
                            v_i_1382_,
                            v_children_1383_,
                        );
                        v___x_1386_ = (leanh::lean_unbox(v___x_1385_) as u8);
                        if v___x_1386_ == 0 {
                            leanh::lean_dec_ref(v_preNode_1372_);
                            v_isSharedCheck_1395_ =
                                (!leanh::lean_is_exclusive(v_x_1374_)) as u8;
                            if v_isSharedCheck_1395_ == 0 {
                                v_unused_1396_ = leanh::lean_ctor_get(v_x_1374_, 0);
                                leanh::lean_dec(v_unused_1396_);
                                v___x_1388_ = v_x_1374_;
                                v_isShared_1389_ = v_isSharedCheck_1395_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_1374_);
                                v___x_1388_ = leanh::lean_box(0);
                                v_isShared_1389_ = v_isSharedCheck_1395_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1397_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1374_, v_i_1382_);
                            v___x_1398_ = l_Lean_PersistentArray_toList___redArg(v_children_1383_);
                            v___x_1399_ = leanh::lean_box(0);
                            leanh::lean_inc(v_postNode_1373_);
                            v___x_1400_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_1372_, v_postNode_1373_, v___x_1397_, v___x_1398_, v___x_1399_);
                            v___x_1401_ = leanh::lean_apply_4(
                                v_postNode_1373_,
                                v_val_1384_,
                                v_i_1382_,
                                v_children_1383_,
                                v___x_1400_,
                            );
                            v___x_1402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1402_, 0, v___x_1401_);
                            return v___x_1402_;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref_known(v_x_1375_, 1);
                    leanh::lean_dec(v_x_1374_);
                    leanh::lean_dec(v_postNode_1373_);
                    leanh::lean_dec_ref(v_preNode_1372_);
                    v___x_1403_ = leanh::lean_box(0);
                    return v___x_1403_;
                }
            },
            1 => {
                v___x_1390_ = leanh::lean_box(0);
                v___x_1391_ = leanh::lean_apply_4(
                    v_postNode_1373_,
                    v_val_1384_,
                    v_i_1382_,
                    v_children_1383_,
                    v___x_1390_,
                );
                if v_isShared_1389_ == 0 {
                    leanh::lean_ctor_set(v___x_1388_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(
    mut v_preNode_1404_: *mut leanh::LeanObject,
    mut v_postNode_1405_: *mut leanh::LeanObject,
    mut v___x_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
    mut v_x_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1407_) == 0 {
                    leanh::lean_dec(v___x_1406_);
                    leanh::lean_dec(v_postNode_1405_);
                    leanh::lean_dec_ref(v_preNode_1404_);
                    v___x_1409_ = l_List_reverse___redArg(v_x_1408_);
                    return v___x_1409_;
                } else {
                    v_head_1410_ = leanh::lean_ctor_get(v_x_1407_, 0);
                    v_tail_1411_ = leanh::lean_ctor_get(v_x_1407_, 1);
                    v_isSharedCheck_1420_ = (!leanh::lean_is_exclusive(v_x_1407_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v___x_1413_ = v_x_1407_;
                        v_isShared_1414_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1411_);
                        leanh::lean_inc(v_head_1410_);
                        leanh::lean_dec(v_x_1407_);
                        v___x_1413_ = leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_1406_);
                leanh::lean_inc(v_postNode_1405_);
                leanh::lean_inc_ref(v_preNode_1404_);
                v___x_1415_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_1404_, v_postNode_1405_, v___x_1406_, v_head_1410_);
                if v_isShared_1414_ == 0 {
                    leanh::lean_ctor_set(v___x_1413_, 1, v_x_1408_);
                    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1415_);
                    v___x_1417_ = v___x_1413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_x_1408_);
                    v___x_1417_ = v_reuseFailAlloc_1419_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1407_ = v_tail_1411_;
                v_x_1408_ = v___x_1417_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(
    mut v_infoTree_1422_: *mut leanh::LeanObject,
    mut v_gt_1423_: *mut leanh::LeanObject,
    mut v_f_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1425_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg___closed__0;
    v___x_1426_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_choose as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_1426_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1426_, 1, v_gt_1423_);
    leanh::lean_closure_set(v___x_1426_, 2, v_f_1424_);
    v___x_1427_ = leanh::lean_box(0);
    v___x_1428_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v___f_1425_, v___x_1426_, v___x_1427_, v_infoTree_1422_);
    if leanh::lean_obj_tag(v___x_1428_) == 0 {
        return v___x_1427_;
    } else {
        let mut v_val_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1429_ = leanh::lean_ctor_get(v___x_1428_, 0);
        leanh::lean_inc(v_val_1429_);
        leanh::lean_dec_ref_known(v___x_1428_, 1);
        return v_val_1429_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f(
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_infoTree_1431_: *mut leanh::LeanObject,
    mut v_gt_1432_: *mut leanh::LeanObject,
    mut v_f_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_1431_, v_gt_1432_, v_f_1433_);
    return v___x_1434_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0(
    mut v_00_u03b1_1435_: *mut leanh::LeanObject,
    mut v_msg_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg(v_msg_1436_);
    return v___x_1437_;
}
pub unsafe fn l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0(
    mut v_00_u03b1_1438_: *mut leanh::LeanObject,
    mut v_preNode_1439_: *mut leanh::LeanObject,
    mut v_postNode_1440_: *mut leanh::LeanObject,
    mut v_x_1441_: *mut leanh::LeanObject,
    mut v_x_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0___redArg(v_preNode_1439_, v_postNode_1440_, v_x_1441_, v_x_1442_);
    return v___x_1443_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1(
    mut v_00_u03b1_1444_: *mut leanh::LeanObject,
    mut v_preNode_1445_: *mut leanh::LeanObject,
    mut v_postNode_1446_: *mut leanh::LeanObject,
    mut v___x_1447_: *mut leanh::LeanObject,
    mut v_x_1448_: *mut leanh::LeanObject,
    mut v_x_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__1___redArg(v_preNode_1445_, v_postNode_1446_, v___x_1447_, v_x_1448_, v_x_1449_);
    return v___x_1450_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(
    mut v_a_1451_: *mut leanh::LeanObject,
    mut v_b_1452_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_snd_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: u8 = 0;
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: u8 = 0;
    let mut v___y_1460_: u8 = 0;
    let mut v___y_1461_: u8 = 0;
    let mut v___y_1462_: u8 = 0;
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___y_1466_: u8 = 0;
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1453_ = leanh::lean_ctor_get(v_a_1451_, 1);
                v_snd_1454_ = leanh::lean_ctor_get(v_b_1452_, 1);
                v___x_1463_ = l_Lean_Elab_Info_lctx(v_snd_1453_);
                v___x_1464_ = lean_local_ctx_is_empty(v___x_1463_);
                if v___x_1464_ == 0 {
                    v___x_1470_ = l_Lean_Elab_Info_lctx(v_snd_1454_);
                    v___x_1471_ = lean_local_ctx_is_empty(v___x_1470_);
                    if v___x_1471_ == 0 {
                        v___y_1466_ = v___x_1471_;
                        state = 3;
                        continue;
                    } else {
                        return v___x_1471_;
                    }
                } else {
                    v___x_1472_ = 0;
                    v___y_1466_ = v___x_1472_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1457_ = l_Lean_Elab_Info_isSmaller(v_snd_1453_, v_snd_1454_);
                if v___x_1457_ == 0 {
                    v___x_1458_ = l_Lean_Elab_Info_isSmaller(v_snd_1454_, v_snd_1453_);
                    if v___x_1458_ == 0 {
                        return v___x_1458_;
                    } else {
                        return v___x_1457_;
                    }
                } else {
                    return v___y_1456_;
                }
            }
            2 => {
                if v___y_1462_ == 0 {
                    v___y_1456_ = v___y_1461_;
                    state = 1;
                    continue;
                } else {
                    return v___y_1460_;
                }
            }
            3 => {
                v___x_1467_ = 1;
                if v___x_1464_ == 0 {
                    v___y_1460_ = v___y_1466_;
                    v___y_1461_ = v___x_1467_;
                    v___y_1462_ = v___x_1464_;
                    state = 2;
                    continue;
                } else {
                    v___x_1468_ = l_Lean_Elab_Info_lctx(v_snd_1454_);
                    v___x_1469_ = lean_local_ctx_is_empty(v___x_1468_);
                    if v___x_1469_ == 0 {
                        v___y_1460_ = v___y_1466_;
                        v___y_1461_ = v___x_1467_;
                        v___y_1462_ = v___x_1464_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1456_ = v___x_1467_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter___boxed(
    mut v_a_1473_: *mut leanh::LeanObject,
    mut v_b_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1475_: u8 = 0;
    let mut v_r_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f_isBetter(v_a_1473_, v_b_1474_);
    leanh::lean_dec_ref(v_b_1474_);
    leanh::lean_dec_ref(v_a_1473_);
    v_r_1476_ = leanh::lean_box((v_res_1475_) as usize);
    return v_r_1476_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(
    mut v_hoverPos_1477_: *mut leanh::LeanObject,
    mut v_ctx_1478_: *mut leanh::LeanObject,
    mut v_info_1479_: *mut leanh::LeanObject,
    mut v_x_1480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1481_: u8 = 0;
    v___x_1481_ = l_Lean_Elab_Info_occursInOrOnBoundary(v_info_1479_, v_hoverPos_1477_);
    if v___x_1481_ == 0 {
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_info_1479_);
        leanh::lean_dec_ref(v_ctx_1478_);
        v___x_1482_ = leanh::lean_box(0);
        return v___x_1482_;
    } else {
        let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1483_, 0, v_ctx_1478_);
        leanh::lean_ctor_set(v___x_1483_, 1, v_info_1479_);
        v___x_1484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
        return v___x_1484_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed(
    mut v_hoverPos_1485_: *mut leanh::LeanObject,
    mut v_ctx_1486_: *mut leanh::LeanObject,
    mut v_info_1487_: *mut leanh::LeanObject,
    mut v_x_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1489_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0(v_hoverPos_1485_, v_ctx_1486_, v_info_1487_, v_x_1488_);
    leanh::lean_dec_ref(v_x_1488_);
    leanh::lean_dec(v_hoverPos_1485_);
    return v_res_1489_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(
    mut v_hoverPos_1491_: *mut leanh::LeanObject,
    mut v_infoTree_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1493_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_1493_, 0, v_hoverPos_1491_);
    v___x_1494_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f___closed__0;
    v___x_1495_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f___redArg(v_infoTree_1492_, v___x_1494_, v___f_1493_);
    return v___x_1495_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(
    mut v_msg_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = leanh::lean_unsigned_to_nat(0);
    v___x_1498_ = lean_panic_fn_borrowed(v___x_1497_, v_msg_1496_);
    return v___x_1498_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(
    mut v_hoverPos_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = 0;
    v___x_1502_ = l_Lean_Syntax_getRange_x3f(v_x_1500_, v___x_1501_);
    if leanh::lean_obj_tag(v___x_1502_) == 0 {
        return v___x_1501_;
    } else {
        let mut v_val_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: u8 = 0;
        let mut v___x_1505_: u8 = 0;
        v_val_1503_ = leanh::lean_ctor_get(v___x_1502_, 0);
        leanh::lean_inc(v_val_1503_);
        leanh::lean_dec_ref_known(v___x_1502_, 1);
        v___x_1504_ = 1;
        v___x_1505_ = l_Lean_Syntax_Range_contains(v_val_1503_, v_hoverPos_1499_, v___x_1504_);
        leanh::lean_dec(v_val_1503_);
        return v___x_1505_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed(
    mut v_hoverPos_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: u8 = 0;
    let mut v_r_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0(v_hoverPos_1506_, v_x_1507_);
    leanh::lean_dec(v_x_1507_);
    leanh::lean_dec(v_hoverPos_1506_);
    v_r_1509_ = leanh::lean_box((v_res_1508_) as usize);
    return v_r_1509_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(
    mut v_stx_1510_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1511_: u8 = 0;
    v___x_1511_ = l_Lean_Syntax_hasArgs(v_stx_1510_);
    if v___x_1511_ == 0 {
        let mut v___x_1512_: u8 = 0;
        v___x_1512_ = 1;
        return v___x_1512_;
    } else {
        let mut v___x_1513_: u8 = 0;
        v___x_1513_ = 0;
        return v___x_1513_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1___boxed(
    mut v_stx_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__1(v_stx_1514_);
    leanh::lean_dec(v_stx_1514_);
    v_r_1516_ = leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(
    mut v_x_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: u8 = 0;
    let mut v_fst_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___y_1539_: u8 = 0;
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1529_) == 0 {
                    return v_x_1529_;
                } else {
                    v_head_1530_ = leanh::lean_ctor_get(v_x_1529_, 0);
                    v_tail_1531_ = leanh::lean_ctor_get(v_x_1529_, 1);
                    v_fst_1535_ = leanh::lean_ctor_get(v_head_1530_, 0);
                    v___x_1536_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1;
                    leanh::lean_inc(v_fst_1535_);
                    v___x_1537_ = l_Lean_Syntax_isOfKind(v_fst_1535_, v___x_1536_);
                    if v___x_1537_ == 0 {
                        v___x_1541_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6;
                        leanh::lean_inc(v_fst_1535_);
                        v___x_1542_ = l_Lean_Syntax_isOfKind(v_fst_1535_, v___x_1541_);
                        if v___x_1542_ == 0 {
                            v___y_1539_ = v___x_1537_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1543_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1544_ = l_Lean_Syntax_getArg(v_fst_1535_, v___x_1543_);
                            v___x_1545_ = l_Lean_Syntax_isOfKind(v___x_1544_, v___x_1536_);
                            if v___x_1545_ == 0 {
                                v___y_1539_ = v___x_1545_;
                                state = 2;
                                continue;
                            } else {
                                v___y_1533_ = v___x_1537_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        return v_x_1529_;
                    }
                }
            }
            1 => {
                if v___y_1533_ == 0 {
                    return v_x_1529_;
                } else {
                    leanh::lean_inc(v_tail_1531_);
                    leanh::lean_dec_ref_known(v_x_1529_, 2);
                    v_x_1529_ = v_tail_1531_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1539_ == 0 {
                    leanh::lean_inc(v_tail_1531_);
                    leanh::lean_dec_ref_known(v_x_1529_, 2);
                    v_x_1529_ = v_tail_1531_;
                    state = 0;
                    continue;
                } else {
                    v___y_1533_ = v___x_1537_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(
    mut v_x_1552_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1553_: u8 = 0;
    let mut v_head_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: u8 = 0;
    let mut v_fst_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1552_) == 0 {
                    v___x_1553_ = 0;
                    return v___x_1553_;
                } else {
                    v_head_1554_ = leanh::lean_ctor_get(v_x_1552_, 0);
                    leanh::lean_inc(v_head_1554_);
                    v_tail_1555_ = leanh::lean_ctor_get(v_x_1552_, 1);
                    leanh::lean_inc(v_tail_1555_);
                    leanh::lean_dec_ref_known(v_x_1552_, 2);
                    v_fst_1559_ = leanh::lean_ctor_get(v_head_1554_, 0);
                    leanh::lean_inc_n(v_fst_1559_, 2);
                    leanh::lean_dec(v_head_1554_);
                    v___x_1560_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___closed__1;
                    v___x_1561_ = l_Lean_Syntax_isOfKind(v_fst_1559_, v___x_1560_);
                    if v___x_1561_ == 0 {
                        leanh::lean_dec(v_fst_1559_);
                        v___y_1557_ = v___x_1561_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1562_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1563_ = l_Lean_Syntax_getArg(v_fst_1559_, v___x_1562_);
                        leanh::lean_dec(v_fst_1559_);
                        v___x_1564_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1;
                        v___x_1565_ = l_Lean_Syntax_isOfKind(v___x_1563_, v___x_1564_);
                        v___y_1557_ = v___x_1565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1557_ == 0 {
                    v_x_1552_ = v_tail_1555_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_1555_);
                    return v___y_1557_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1___boxed(
    mut v_x_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1567_: u8 = 0;
    let mut v_r_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1567_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_x_1566_);
    v_r_1568_ = leanh::lean_box((v_res_1567_) as usize);
    return v_r_1568_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__3;
    v___x_1574_ = leanh::lean_unsigned_to_nat(14);
    v___x_1575_ = leanh::lean_unsigned_to_nat(22);
    v___x_1576_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__2;
    v___x_1577_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__1;
    v___x_1578_ = l_mkPanicMessageWithDecl(
        v___x_1577_,
        v___x_1576_,
        v___x_1575_,
        v___x_1574_,
        v___x_1573_,
    );
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(
    mut v_hoverPos_1579_: *mut leanh::LeanObject,
    mut v_infoTree_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v_stack_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v_fst_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: u8 = 0;
    let mut v___y_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: u8 = 0;
    let mut v___y_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDotIdCompletion_1621_: u8 = 0;
    let mut v_fst_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1624_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_hoverPos_1579_);
                v___x_1581_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findClosestInfoWithLocalContextAt_x3f(v_hoverPos_1579_, v_infoTree_1580_);
                if leanh::lean_obj_tag(v___x_1581_) == 1 {
                    v_val_1582_ = leanh::lean_ctor_get(v___x_1581_, 0);
                    leanh::lean_inc(v_val_1582_);
                    leanh::lean_dec_ref_known(v___x_1581_, 1);
                    v_fst_1583_ = leanh::lean_ctor_get(v_val_1582_, 0);
                    leanh::lean_inc(v_fst_1583_);
                    v_snd_1584_ = leanh::lean_ctor_get(v_val_1582_, 1);
                    leanh::lean_inc(v_snd_1584_);
                    leanh::lean_dec(v_val_1582_);
                    leanh::lean_inc(v_hoverPos_1579_);
                    v___f_1585_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_1585_, 0, v_hoverPos_1579_);
                    v___f_1586_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__0;
                    v___x_1587_ = l_Lean_Elab_Info_stx(v_snd_1584_);
                    v___x_1588_ =
                        l_Lean_Syntax_findStack_x3f(v___x_1587_, v___f_1585_, v___f_1586_);
                    if leanh::lean_obj_tag(v___x_1588_) == 1 {
                        v_val_1589_ = leanh::lean_ctor_get(v___x_1588_, 0);
                        v_isSharedCheck_1643_ =
                            (!leanh::lean_is_exclusive(v___x_1588_)) as u8;
                        if v_isSharedCheck_1643_ == 0 {
                            v___x_1591_ = v___x_1588_;
                            v_isShared_1592_ = v_isSharedCheck_1643_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1589_);
                            leanh::lean_dec(v___x_1588_);
                            v___x_1591_ = leanh::lean_box(0);
                            v_isShared_1592_ = v_isSharedCheck_1643_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1588_);
                        leanh::lean_dec(v_snd_1584_);
                        leanh::lean_dec(v_fst_1583_);
                        leanh::lean_dec(v_hoverPos_1579_);
                        v___x_1644_ = leanh::lean_box(0);
                        return v___x_1644_;
                    }
                } else {
                    leanh::lean_dec(v___x_1581_);
                    leanh::lean_dec(v_hoverPos_1579_);
                    v___x_1645_ = leanh::lean_box(0);
                    return v___x_1645_;
                }
            }
            1 => {
                v_stack_1593_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0(v_val_1589_);
                v___x_1594_ = l_List_head_x3f___redArg(v_stack_1593_);
                if leanh::lean_obj_tag(v___x_1594_) == 1 {
                    v_val_1595_ = leanh::lean_ctor_get(v___x_1594_, 0);
                    v_isSharedCheck_1641_ = (!leanh::lean_is_exclusive(v___x_1594_)) as u8;
                    if v_isSharedCheck_1641_ == 0 {
                        v___x_1597_ = v___x_1594_;
                        v_isShared_1598_ = v_isSharedCheck_1641_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1595_);
                        leanh::lean_dec(v___x_1594_);
                        v___x_1597_ = leanh::lean_box(0);
                        v_isShared_1598_ = v_isSharedCheck_1641_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1594_);
                    leanh::lean_dec(v_stack_1593_);
                    leanh::lean_del_object(v___x_1591_);
                    leanh::lean_dec(v_snd_1584_);
                    leanh::lean_dec(v_fst_1583_);
                    leanh::lean_dec(v_hoverPos_1579_);
                    v___x_1642_ = leanh::lean_box(0);
                    return v___x_1642_;
                }
            }
            2 => {
                v_fst_1599_ = leanh::lean_ctor_get(v_val_1595_, 0);
                leanh::lean_inc(v_fst_1599_);
                leanh::lean_dec(v_val_1595_);
                v_isDotIdCompletion_1621_ = l_List_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__1(v_stack_1593_);
                if v_isDotIdCompletion_1621_ == 0 {
                    v___x_1629_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__1;
                    leanh::lean_inc(v_fst_1599_);
                    v___x_1630_ = l_Lean_Syntax_isOfKind(v_fst_1599_, v___x_1629_);
                    if v___x_1630_ == 0 {
                        v___x_1631_ = l_List_dropWhile___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__0___closed__6;
                        leanh::lean_inc(v_fst_1599_);
                        v___x_1632_ = l_Lean_Syntax_isOfKind(v_fst_1599_, v___x_1631_);
                        if v___x_1632_ == 0 {
                            leanh::lean_dec(v_fst_1599_);
                            leanh::lean_del_object(v___x_1597_);
                            leanh::lean_del_object(v___x_1591_);
                            leanh::lean_dec(v_snd_1584_);
                            leanh::lean_dec(v_fst_1583_);
                            leanh::lean_dec(v_hoverPos_1579_);
                            v___x_1633_ = leanh::lean_box(0);
                            return v___x_1633_;
                        } else {
                            v___x_1634_ = leanh::lean_unsigned_to_nat(0);
                            v_id_1635_ = l_Lean_Syntax_getArg(v_fst_1599_, v___x_1634_);
                            leanh::lean_inc(v_id_1635_);
                            v___x_1636_ = l_Lean_Syntax_isOfKind(v_id_1635_, v___x_1629_);
                            if v___x_1636_ == 0 {
                                leanh::lean_dec(v_id_1635_);
                                leanh::lean_dec(v_fst_1599_);
                                leanh::lean_del_object(v___x_1597_);
                                leanh::lean_del_object(v___x_1591_);
                                leanh::lean_dec(v_snd_1584_);
                                leanh::lean_dec(v_fst_1583_);
                                leanh::lean_dec(v_hoverPos_1579_);
                                v___x_1637_ = leanh::lean_box(0);
                                return v___x_1637_;
                            } else {
                                v___x_1638_ = l_Lean_TSyntax_getId(v_id_1635_);
                                leanh::lean_dec(v_id_1635_);
                                v_fst_1623_ = v___x_1638_;
                                v_snd_1624_ = v___x_1636_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v___x_1639_ = l_Lean_TSyntax_getId(v_fst_1599_);
                        v_fst_1623_ = v___x_1639_;
                        v_snd_1624_ = v_isDotIdCompletion_1621_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1599_);
                    leanh::lean_del_object(v___x_1597_);
                    leanh::lean_del_object(v___x_1591_);
                    leanh::lean_dec(v_snd_1584_);
                    leanh::lean_dec(v_fst_1583_);
                    leanh::lean_dec(v_hoverPos_1579_);
                    v___x_1640_ = leanh::lean_box(0);
                    return v___x_1640_;
                }
            }
            3 => {
                v___x_1604_ = l_Lean_Elab_Info_lctx(v_snd_1584_);
                leanh::lean_dec(v_snd_1584_);
                v___x_1605_ = leanh::lean_box(0);
                v___x_1606_ = leanh::lean_alloc_ctor(1, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_1606_, 0, v_fst_1599_);
                leanh::lean_ctor_set(v___x_1606_, 1, v___y_1602_);
                leanh::lean_ctor_set(v___x_1606_, 2, v___x_1604_);
                leanh::lean_ctor_set(v___x_1606_, 3, v___x_1605_);
                leanh::lean_ctor_set_uint8(
                    v___x_1606_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_1601_,
                );
                v___x_1607_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1607_, 0, v___y_1603_);
                leanh::lean_ctor_set(v___x_1607_, 1, v_fst_1583_);
                leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
                if v_isShared_1598_ == 0 {
                    leanh::lean_ctor_set(v___x_1597_, 0, v___x_1607_);
                    v___x_1609_ = v___x_1597_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
                    v___x_1609_ = v_reuseFailAlloc_1610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1609_;
            }
            5 => {
                v___x_1615_ = lean_nat_dec_lt(v_hoverPos_1579_, v___y_1614_);
                if v___x_1615_ == 0 {
                    leanh::lean_dec(v___y_1614_);
                    leanh::lean_del_object(v___x_1591_);
                    leanh::lean_dec(v_hoverPos_1579_);
                    v___x_1616_ = leanh::lean_box(0);
                    v___y_1601_ = v___y_1612_;
                    v___y_1602_ = v___y_1613_;
                    v___y_1603_ = v___x_1616_;
                    state = 3;
                    continue;
                } else {
                    v___x_1617_ = lean_nat_sub(v___y_1614_, v_hoverPos_1579_);
                    leanh::lean_dec(v_hoverPos_1579_);
                    leanh::lean_dec(v___y_1614_);
                    if v_isShared_1592_ == 0 {
                        leanh::lean_ctor_set(v___x_1591_, 0, v___x_1617_);
                        v___x_1619_ = v___x_1591_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
                        v___x_1619_ = v_reuseFailAlloc_1620_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___y_1601_ = v___y_1612_;
                v___y_1602_ = v___y_1613_;
                v___y_1603_ = v___x_1619_;
                state = 3;
                continue;
            }
            7 => {
                v___x_1625_ = l_Lean_Syntax_getTailPos_x3f(v_fst_1599_, v_isDotIdCompletion_1621_);
                if leanh::lean_obj_tag(v___x_1625_) == 0 {
                    v___x_1626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once), _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
                    v___x_1627_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f_spec__2(v___x_1626_);
                    v___y_1612_ = v_snd_1624_;
                    v___y_1613_ = v_fst_1623_;
                    v___y_1614_ = v___x_1627_;
                    state = 5;
                    continue;
                } else {
                    v_val_1628_ = leanh::lean_ctor_get(v___x_1625_, 0);
                    leanh::lean_inc(v_val_1628_);
                    leanh::lean_dec_ref_known(v___x_1625_, 1);
                    v___y_1612_ = v_snd_1624_;
                    v___y_1613_ = v_fst_1623_;
                    v___y_1614_ = v_val_1628_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(
    mut v_fileMap_1646_: *mut leanh::LeanObject,
    mut v_hoverPos_1647_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_source_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1650_: u32 = 0;
    let mut v___y_1652_: u8 = 0;
    let mut v___x_1653_: u32 = 0;
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: u32 = 0;
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: u32 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u32 = 0;
    let mut v___x_1660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_1648_ = leanh::lean_ctor_get(v_fileMap_1646_, 0);
                v___x_1649_ = lean_string_utf8_at_end(v_source_1648_, v_hoverPos_1647_);
                if v___x_1649_ == 0 {
                    v___x_1650_ = lean_string_utf8_get(v_source_1648_, v_hoverPos_1647_);
                    v___x_1657_ = 32;
                    v___x_1658_ = lean_uint32_dec_eq(v___x_1650_, v___x_1657_);
                    if v___x_1658_ == 0 {
                        v___x_1659_ = 9;
                        v___x_1660_ = lean_uint32_dec_eq(v___x_1650_, v___x_1659_);
                        v___y_1652_ = v___x_1660_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1652_ = v___x_1658_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1649_;
                }
            }
            1 => {
                if v___y_1652_ == 0 {
                    v___x_1653_ = 13;
                    v___x_1654_ = lean_uint32_dec_eq(v___x_1650_, v___x_1653_);
                    if v___x_1654_ == 0 {
                        v___x_1655_ = 10;
                        v___x_1656_ = lean_uint32_dec_eq(v___x_1650_, v___x_1655_);
                        return v___x_1656_;
                    } else {
                        return v___x_1654_;
                    }
                } else {
                    return v___y_1652_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace___boxed(
    mut v_fileMap_1661_: *mut leanh::LeanObject,
    mut v_hoverPos_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: u8 = 0;
    let mut v_r_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1661_, v_hoverPos_1662_);
    leanh::lean_dec(v_hoverPos_1662_);
    leanh::lean_dec_ref(v_fileMap_1661_);
    v_r_1664_ = leanh::lean_box((v_res_1663_) as usize);
    return v_r_1664_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(
    mut v_fileMap_1665_: *mut leanh::LeanObject,
    mut v_hoverPos_1666_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_1668_: u32 = 0;
    let mut v___y_1669_: u8 = 0;
    let mut v___x_1670_: u32 = 0;
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: u32 = 0;
    let mut v___x_1673_: u8 = 0;
    let mut v_source_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u32 = 0;
    let mut v___x_1679_: u32 = 0;
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: u32 = 0;
    let mut v___x_1682_: u8 = 0;
    let mut v___y_1684_: u8 = 0;
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: u32 = 0;
    let mut v___y_1688_: u8 = 0;
    let mut v___x_1689_: u32 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: u32 = 0;
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: u32 = 0;
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: u32 = 0;
    let mut v___x_1696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_1674_ = leanh::lean_ctor_get(v_fileMap_1665_, 0);
                v___x_1685_ = lean_string_utf8_at_end(v_source_1674_, v_hoverPos_1666_);
                if v___x_1685_ == 0 {
                    v___x_1686_ = lean_string_utf8_get(v_source_1674_, v_hoverPos_1666_);
                    v___x_1693_ = 32;
                    v___x_1694_ = lean_uint32_dec_eq(v___x_1686_, v___x_1693_);
                    if v___x_1694_ == 0 {
                        v___x_1695_ = 9;
                        v___x_1696_ = lean_uint32_dec_eq(v___x_1686_, v___x_1695_);
                        v___y_1688_ = v___x_1696_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1688_ = v___x_1694_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_1684_ = v___x_1685_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_1669_ == 0 {
                    v___x_1670_ = 13;
                    v___x_1671_ = lean_uint32_dec_eq(v___y_1668_, v___x_1670_);
                    if v___x_1671_ == 0 {
                        v___x_1672_ = 10;
                        v___x_1673_ = lean_uint32_dec_eq(v___y_1668_, v___x_1672_);
                        return v___x_1673_;
                    } else {
                        return v___x_1671_;
                    }
                } else {
                    return v___y_1669_;
                }
            }
            2 => {
                v___x_1676_ = leanh::lean_unsigned_to_nat(1);
                v___x_1677_ = lean_nat_sub(v_hoverPos_1666_, v___x_1676_);
                v___x_1678_ = lean_string_utf8_get(v_source_1674_, v___x_1677_);
                leanh::lean_dec(v___x_1677_);
                v___x_1679_ = 32;
                v___x_1680_ = lean_uint32_dec_eq(v___x_1678_, v___x_1679_);
                if v___x_1680_ == 0 {
                    v___x_1681_ = 9;
                    v___x_1682_ = lean_uint32_dec_eq(v___x_1678_, v___x_1681_);
                    v___y_1668_ = v___x_1678_;
                    v___y_1669_ = v___x_1682_;
                    state = 1;
                    continue;
                } else {
                    v___y_1668_ = v___x_1678_;
                    v___y_1669_ = v___x_1680_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1684_ == 0 {
                    return v___y_1684_;
                } else {
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_1688_ == 0 {
                    v___x_1689_ = 13;
                    v___x_1690_ = lean_uint32_dec_eq(v___x_1686_, v___x_1689_);
                    if v___x_1690_ == 0 {
                        v___x_1691_ = 10;
                        v___x_1692_ = lean_uint32_dec_eq(v___x_1686_, v___x_1691_);
                        v___y_1684_ = v___x_1692_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1684_ = v___x_1690_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace___boxed(
    mut v_fileMap_1697_: *mut leanh::LeanObject,
    mut v_hoverPos_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1699_: u8 = 0;
    let mut v_r_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1697_, v_hoverPos_1698_);
    leanh::lean_dec(v_hoverPos_1698_);
    leanh::lean_dec_ref(v_fileMap_1697_);
    v_r_1700_ = leanh::lean_box((v_res_1699_) as usize);
    return v_r_1700_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(
    mut v_stx_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    leanh::lean_inc(v_stx_1714_);
    v___x_1715_ = l_Lean_Syntax_getKind(v_stx_1714_);
    v___x_1716_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2;
    v___x_1717_ = lean_name_eq(v___x_1715_, v___x_1716_);
    if v___x_1717_ == 0 {
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: u8 = 0;
        v___x_1718_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4;
        v___x_1719_ = lean_name_eq(v___x_1715_, v___x_1718_);
        leanh::lean_dec(v___x_1715_);
        if v___x_1719_ == 0 {
            let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_stx_1714_);
            v___x_1720_ = leanh::lean_box(0);
            return v___x_1720_;
        } else {
            let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1721_ = leanh::lean_unsigned_to_nat(1);
            v___x_1722_ = l_Lean_Syntax_getArg(v_stx_1714_, v___x_1721_);
            leanh::lean_dec(v_stx_1714_);
            v___x_1723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1723_, 0, v___x_1722_);
            return v___x_1723_;
        }
    } else {
        let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1715_);
        v___x_1724_ = leanh::lean_unsigned_to_nat(0);
        v___x_1725_ = l_Lean_Syntax_getArg(v_stx_1714_, v___x_1724_);
        leanh::lean_dec(v_stx_1714_);
        v___x_1726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1726_, 0, v___x_1725_);
        return v___x_1726_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(
    mut v_fileMap_1727_: *mut leanh::LeanObject,
    mut v_hoverPos_1728_: *mut leanh::LeanObject,
    mut v_hoverFilePos_1729_: *mut leanh::LeanObject,
    mut v_stx_1730_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_1730_);
    if leanh::lean_obj_tag(v___x_1731_) == 1 {
        let mut v_val_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: u8 = 0;
        let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1732_ = leanh::lean_ctor_get(v___x_1731_, 0);
        leanh::lean_inc(v_val_1732_);
        leanh::lean_dec_ref_known(v___x_1731_, 1);
        v___x_1733_ = 0;
        v___x_1734_ = l_Lean_Syntax_getPos_x3f(v_val_1732_, v___x_1733_);
        leanh::lean_dec(v_val_1732_);
        if leanh::lean_obj_tag(v___x_1734_) == 1 {
            let mut v_val_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_column_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_column_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1739_: u8 = 0;
            v_val_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
            leanh::lean_inc(v_val_1735_);
            leanh::lean_dec_ref_known(v___x_1734_, 1);
            leanh::lean_inc_ref(v_fileMap_1727_);
            v___x_1736_ = l_Lean_FileMap_toPosition(v_fileMap_1727_, v_val_1735_);
            leanh::lean_dec(v_val_1735_);
            v_column_1737_ = leanh::lean_ctor_get(v___x_1736_, 1);
            leanh::lean_inc(v_column_1737_);
            leanh::lean_dec_ref(v___x_1736_);
            v_column_1738_ = leanh::lean_ctor_get(v_hoverFilePos_1729_, 1);
            v___x_1739_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1727_, v_hoverPos_1728_);
            leanh::lean_dec_ref(v_fileMap_1727_);
            if v___x_1739_ == 0 {
                leanh::lean_dec(v_column_1737_);
                return v___x_1739_;
            } else {
                let mut v_isCursorInTacticBlock_1740_: u8 = 0;
                v_isCursorInTacticBlock_1740_ = lean_nat_dec_eq(v_column_1738_, v_column_1737_);
                leanh::lean_dec(v_column_1737_);
                return v_isCursorInTacticBlock_1740_;
            }
        } else {
            leanh::lean_dec(v___x_1734_);
            leanh::lean_dec_ref(v_fileMap_1727_);
            return v___x_1733_;
        }
    } else {
        let mut v___x_1741_: u8 = 0;
        leanh::lean_dec(v___x_1731_);
        leanh::lean_dec_ref(v_fileMap_1727_);
        v___x_1741_ = 0;
        return v___x_1741_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation___boxed(
    mut v_fileMap_1742_: *mut leanh::LeanObject,
    mut v_hoverPos_1743_: *mut leanh::LeanObject,
    mut v_hoverFilePos_1744_: *mut leanh::LeanObject,
    mut v_stx_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: u8 = 0;
    let mut v_r_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_1742_, v_hoverPos_1743_, v_hoverFilePos_1744_, v_stx_1745_);
    leanh::lean_dec_ref(v_hoverFilePos_1744_);
    leanh::lean_dec(v_hoverPos_1743_);
    v_r_1747_ = leanh::lean_box((v_res_1746_) as usize);
    return v_r_1747_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(
    mut v_hoverPos_1749_: *mut leanh::LeanObject,
    mut v_as_1750_: *mut leanh::LeanObject,
    mut v_i_1751_: usize,
    mut v_stop_1752_: usize,
) -> u8 {
    let mut v___x_1754_: usize = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: u8 = 0;
    let mut v___y_1760_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: u8 = 0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1757_ = lean_usize_dec_eq(v_i_1751_, v_stop_1752_);
                if v___x_1757_ == 0 {
                    v___x_1758_ = 1;
                    v___x_1761_ = lean_array_uget_borrowed(v_as_1750_, v_i_1751_);
                    v___x_1762_ = l_Lean_Syntax_getTailPos_x3f(v___x_1761_, v___x_1757_);
                    if leanh::lean_obj_tag(v___x_1762_) == 1 {
                        v_val_1763_ = leanh::lean_ctor_get(v___x_1762_, 0);
                        leanh::lean_inc(v_val_1763_);
                        leanh::lean_dec_ref_known(v___x_1762_, 1);
                        v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___closed__0;
                        leanh::lean_inc(v___x_1761_);
                        v___x_1770_ = l_Lean_Syntax_isToken(v___x_1769_, v___x_1761_);
                        if v___x_1770_ == 0 {
                            v___y_1765_ = v___x_1770_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1771_ = lean_nat_dec_le(v_val_1763_, v_hoverPos_1749_);
                            v___y_1765_ = v___x_1771_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1762_);
                        v___y_1760_ = v___x_1757_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1772_ = 0;
                    return v___x_1772_;
                }
            }
            1 => {
                v___x_1754_ = 1usize;
                v___x_1755_ = lean_usize_add(v_i_1751_, v___x_1754_);
                v_i_1751_ = v___x_1755_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1760_ == 0 {
                    state = 1;
                    continue;
                } else {
                    return v___x_1758_;
                }
            }
            3 => {
                if v___y_1765_ == 0 {
                    leanh::lean_dec(v_val_1763_);
                    state = 1;
                    continue;
                } else {
                    v___x_1766_ = l_Lean_Syntax_getTrailingSize(v___x_1761_);
                    v___x_1767_ = lean_nat_add(v_val_1763_, v___x_1766_);
                    leanh::lean_dec(v___x_1766_);
                    leanh::lean_dec(v_val_1763_);
                    v___x_1768_ = lean_nat_dec_le(v_hoverPos_1749_, v___x_1767_);
                    leanh::lean_dec(v___x_1767_);
                    v___y_1760_ = v___x_1768_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0___boxed(
    mut v_hoverPos_1773_: *mut leanh::LeanObject,
    mut v_as_1774_: *mut leanh::LeanObject,
    mut v_i_1775_: *mut leanh::LeanObject,
    mut v_stop_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1777_: usize = 0;
    let mut v_stop_boxed_1778_: usize = 0;
    let mut v_res_1779_: u8 = 0;
    let mut v_r_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1777_ = leanh::lean_unbox_usize(v_i_1775_);
    leanh::lean_dec(v_i_1775_);
    v_stop_boxed_1778_ = leanh::lean_unbox_usize(v_stop_1776_);
    leanh::lean_dec(v_stop_1776_);
    v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_1773_, v_as_1774_, v_i_boxed_1777_, v_stop_boxed_1778_);
    leanh::lean_dec_ref(v_as_1774_);
    leanh::lean_dec(v_hoverPos_1773_);
    v_r_1780_ = leanh::lean_box((v_res_1779_) as usize);
    return v_r_1780_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(
    mut v_fileMap_1781_: *mut leanh::LeanObject,
    mut v_hoverPos_1782_: *mut leanh::LeanObject,
    mut v_stx_1783_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f(v_stx_1783_);
    if leanh::lean_obj_tag(v___x_1784_) == 1 {
        let mut v_val_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: u8 = 0;
        v_val_1785_ = leanh::lean_ctor_get(v___x_1784_, 0);
        leanh::lean_inc(v_val_1785_);
        leanh::lean_dec_ref_known(v___x_1784_, 1);
        v___x_1786_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_1781_, v_hoverPos_1782_);
        if v___x_1786_ == 0 {
            leanh::lean_dec(v_val_1785_);
            return v___x_1786_;
        } else {
            let mut v_tactics_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1790_: u8 = 0;
            v_tactics_1787_ = l_Lean_Syntax_getArgs(v_val_1785_);
            leanh::lean_dec(v_val_1785_);
            v___x_1788_ = leanh::lean_unsigned_to_nat(0);
            v___x_1789_ = lean_array_get_size(v_tactics_1787_);
            v___x_1790_ = lean_nat_dec_lt(v___x_1788_, v___x_1789_);
            if v___x_1790_ == 0 {
                leanh::lean_dec_ref(v_tactics_1787_);
                return v___x_1790_;
            } else {
                if v___x_1790_ == 0 {
                    leanh::lean_dec_ref(v_tactics_1787_);
                    return v___x_1790_;
                } else {
                    let mut v___x_1791_: usize = 0;
                    let mut v___x_1792_: usize = 0;
                    let mut v___x_1793_: u8 = 0;
                    v___x_1791_ = 0usize;
                    v___x_1792_ = lean_usize_of_nat(v___x_1789_);
                    v___x_1793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon_spec__0(v_hoverPos_1782_, v_tactics_1787_, v___x_1791_, v___x_1792_);
                    leanh::lean_dec_ref(v_tactics_1787_);
                    return v___x_1793_;
                }
            }
        }
    } else {
        let mut v___x_1794_: u8 = 0;
        leanh::lean_dec(v___x_1784_);
        v___x_1794_ = 0;
        return v___x_1794_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon___boxed(
    mut v_fileMap_1795_: *mut leanh::LeanObject,
    mut v_hoverPos_1796_: *mut leanh::LeanObject,
    mut v_stx_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: u8 = 0;
    let mut v_r_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_1795_, v_hoverPos_1796_, v_stx_1797_);
    leanh::lean_dec(v_hoverPos_1796_);
    leanh::lean_dec_ref(v_fileMap_1795_);
    v_r_1799_ = leanh::lean_box((v_res_1798_) as usize);
    return v_r_1799_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(
    mut v_fileMap_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v_source_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v___x_1809_: u32 = 0;
    let mut v___x_1810_: u32 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1802_ = leanh::lean_ctor_get(v_a_1801_, 0);
                v_snd_1803_ = leanh::lean_ctor_get(v_a_1801_, 1);
                v_isSharedCheck_1825_ = (!leanh::lean_is_exclusive(v_a_1801_)) as u8;
                if v_isSharedCheck_1825_ == 0 {
                    v___x_1805_ = v_a_1801_;
                    v_isShared_1806_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1803_);
                    leanh::lean_inc(v_fst_1802_);
                    leanh::lean_dec(v_a_1801_);
                    v___x_1805_ = leanh::lean_box(0);
                    v_isShared_1806_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_source_1807_ = leanh::lean_ctor_get(v_fileMap_1800_, 0);
                v___x_1808_ = lean_string_utf8_at_end(v_source_1807_, v_fst_1802_);
                if v___x_1808_ == 0 {
                    v___x_1809_ = lean_string_utf8_get(v_source_1807_, v_fst_1802_);
                    v___x_1810_ = 32;
                    v___x_1811_ = lean_uint32_dec_eq(v___x_1809_, v___x_1810_);
                    if v___x_1811_ == 0 {
                        if v_isShared_1806_ == 0 {
                            v___x_1813_ = v___x_1805_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1814_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_fst_1802_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_snd_1803_);
                            v___x_1813_ = v_reuseFailAlloc_1814_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1815_ = lean_string_utf8_next(v_source_1807_, v_fst_1802_);
                        leanh::lean_dec(v_fst_1802_);
                        v___x_1816_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1817_ = lean_nat_add(v_snd_1803_, v___x_1816_);
                        leanh::lean_dec(v_snd_1803_);
                        if v_isShared_1806_ == 0 {
                            leanh::lean_ctor_set(v___x_1805_, 1, v___x_1817_);
                            leanh::lean_ctor_set(v___x_1805_, 0, v___x_1815_);
                            v___x_1819_ = v___x_1805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1821_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1817_);
                            v___x_1819_ = v_reuseFailAlloc_1821_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_1806_ == 0 {
                        v___x_1823_ = v___x_1805_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_fst_1802_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_snd_1803_);
                        v___x_1823_ = v_reuseFailAlloc_1824_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1813_;
            }
            3 => {
                v_a_1801_ = v___x_1819_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg___boxed(
    mut v_fileMap_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_1826_, v_a_1827_);
    leanh::lean_dec_ref(v_fileMap_1826_);
    return v_res_1828_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(
    mut v_fileMap_1829_: *mut leanh::LeanObject,
    mut v_pos_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_1831_ = leanh::lean_unsigned_to_nat(0);
    v___x_1832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1832_, 0, v_pos_1830_);
    leanh::lean_ctor_set(v___x_1832_, 1, v_n_1831_);
    v___x_1833_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_1829_, v___x_1832_);
    v_snd_1834_ = leanh::lean_ctor_get(v___x_1833_, 1);
    leanh::lean_inc(v_snd_1834_);
    leanh::lean_dec_ref(v___x_1833_);
    return v_snd_1834_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces___boxed(
    mut v_fileMap_1835_: *mut leanh::LeanObject,
    mut v_pos_1836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1837_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_1835_, v_pos_1836_);
    leanh::lean_dec_ref(v_fileMap_1835_);
    return v_res_1837_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(
    mut v_fileMap_1838_: *mut leanh::LeanObject,
    mut v_inst_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___redArg(v_fileMap_1838_, v_a_1840_);
    return v___x_1841_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0___boxed(
    mut v_fileMap_1842_: *mut leanh::LeanObject,
    mut v_inst_1843_: *mut leanh::LeanObject,
    mut v_a_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces_spec__0(v_fileMap_1842_, v_inst_1843_, v_a_1844_);
    leanh::lean_dec_ref(v_fileMap_1842_);
    return v_res_1845_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(
    mut v_fileMap_1846_: *mut leanh::LeanObject,
    mut v_hoverPos_1847_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_1848_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_leadingTokenTailPos_x3f_1848_) == 1 {
        let mut v_val_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_hoverFilePos_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_line_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_column_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tokenTailFilePos_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_line_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: u8 = 0;
        v_val_1849_ = leanh::lean_ctor_get(v_leadingTokenTailPos_x3f_1848_, 0);
        leanh::lean_inc_ref_n(v_fileMap_1846_, 2);
        v_hoverFilePos_1850_ = l_Lean_FileMap_toPosition(v_fileMap_1846_, v_hoverPos_1847_);
        v_line_1851_ = leanh::lean_ctor_get(v_hoverFilePos_1850_, 0);
        leanh::lean_inc(v_line_1851_);
        v_column_1852_ = leanh::lean_ctor_get(v_hoverFilePos_1850_, 1);
        leanh::lean_inc(v_column_1852_);
        leanh::lean_dec_ref(v_hoverFilePos_1850_);
        v_tokenTailFilePos_1853_ = l_Lean_FileMap_toPosition(v_fileMap_1846_, v_val_1849_);
        v_line_1854_ = leanh::lean_ctor_get(v_tokenTailFilePos_1853_, 0);
        leanh::lean_inc(v_line_1854_);
        leanh::lean_dec_ref(v_tokenTailFilePos_1853_);
        v___x_1855_ = lean_nat_dec_eq(v_line_1851_, v_line_1854_);
        leanh::lean_dec(v_line_1851_);
        if v___x_1855_ == 0 {
            let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedColumn_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1860_: u8 = 0;
            v___x_1856_ = l_Lean_FileMap_lineStart(v_fileMap_1846_, v_line_1854_);
            leanh::lean_dec(v_line_1854_);
            v___x_1857_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_countLeadingSpaces(v_fileMap_1846_, v___x_1856_);
            leanh::lean_dec_ref(v_fileMap_1846_);
            v___x_1858_ = leanh::lean_unsigned_to_nat(2);
            v_expectedColumn_1859_ = lean_nat_add(v___x_1857_, v___x_1858_);
            leanh::lean_dec(v___x_1857_);
            v___x_1860_ = lean_nat_dec_eq(v_column_1852_, v_expectedColumn_1859_);
            leanh::lean_dec(v_expectedColumn_1859_);
            leanh::lean_dec(v_column_1852_);
            return v___x_1860_;
        } else {
            let mut v___x_1861_: u8 = 0;
            leanh::lean_dec(v_line_1854_);
            leanh::lean_dec(v_column_1852_);
            leanh::lean_dec_ref(v_fileMap_1846_);
            v___x_1861_ = lean_nat_dec_le(v_val_1849_, v_hoverPos_1847_);
            return v___x_1861_;
        }
    } else {
        let mut v___x_1862_: u8 = 0;
        leanh::lean_dec_ref(v_fileMap_1846_);
        v___x_1862_ = 1;
        return v___x_1862_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation___boxed(
    mut v_fileMap_1863_: *mut leanh::LeanObject,
    mut v_hoverPos_1864_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1866_: u8 = 0;
    let mut v_r_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_1863_, v_hoverPos_1864_, v_leadingTokenTailPos_x3f_1865_);
    leanh::lean_dec(v_leadingTokenTailPos_x3f_1865_);
    leanh::lean_dec(v_hoverPos_1864_);
    v_r_1867_ = leanh::lean_box((v_res_1866_) as usize);
    return v_r_1867_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(
    mut v_a_1868_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_a_1868_) {
        0 => {
            let mut v___x_1869_: u8 = 0;
            v___x_1869_ = 1;
            return v___x_1869_;
        }
        1 => {
            let mut v_args_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1873_: u8 = 0;
            v_args_1870_ = leanh::lean_ctor_get(v_a_1868_, 2);
            v___x_1871_ = leanh::lean_unsigned_to_nat(0);
            v___x_1872_ = lean_array_get_size(v_args_1870_);
            v___x_1873_ = lean_nat_dec_lt(v___x_1871_, v___x_1872_);
            if v___x_1873_ == 0 {
                let mut v___x_1874_: u8 = 0;
                v___x_1874_ = 1;
                return v___x_1874_;
            } else {
                if v___x_1873_ == 0 {
                    return v___x_1873_;
                } else {
                    let mut v___x_1875_: usize = 0;
                    let mut v___x_1876_: usize = 0;
                    let mut v___x_1877_: u8 = 0;
                    v___x_1875_ = 0usize;
                    v___x_1876_ = lean_usize_of_nat(v___x_1872_);
                    v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_args_1870_, v___x_1875_, v___x_1876_);
                    if v___x_1877_ == 0 {
                        return v___x_1873_;
                    } else {
                        let mut v___x_1878_: u8 = 0;
                        v___x_1878_ = 0;
                        return v___x_1878_;
                    }
                }
            }
        }
        _ => {
            let mut v___x_1879_: u8 = 0;
            v___x_1879_ = 0;
            return v___x_1879_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(
    mut v_as_1880_: *mut leanh::LeanObject,
    mut v_i_1881_: usize,
    mut v_stop_1882_: usize,
) -> u8 {
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: usize = 0;
    let mut v___x_1888_: usize = 0;
    let mut v___x_1890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = lean_usize_dec_eq(v_i_1881_, v_stop_1882_);
                if v___x_1883_ == 0 {
                    v___x_1884_ = 1;
                    v___x_1885_ = lean_array_uget_borrowed(v_as_1880_, v_i_1881_);
                    v___x_1886_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_1885_);
                    if v___x_1886_ == 0 {
                        return v___x_1884_;
                    } else {
                        if v___x_1883_ == 0 {
                            v___x_1887_ = 1usize;
                            v___x_1888_ = lean_usize_add(v_i_1881_, v___x_1887_);
                            v_i_1881_ = v___x_1888_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1884_;
                        }
                    }
                } else {
                    v___x_1890_ = 0;
                    return v___x_1890_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0___boxed(
    mut v_as_1891_: *mut leanh::LeanObject,
    mut v_i_1892_: *mut leanh::LeanObject,
    mut v_stop_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1894_: usize = 0;
    let mut v_stop_boxed_1895_: usize = 0;
    let mut v_res_1896_: u8 = 0;
    let mut v_r_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1894_ = leanh::lean_unbox_usize(v_i_1892_);
    leanh::lean_dec(v_i_1892_);
    v_stop_boxed_1895_ = leanh::lean_unbox_usize(v_stop_1893_);
    leanh::lean_dec(v_stop_1893_);
    v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty_spec__0(v_as_1891_, v_i_boxed_1894_, v_stop_boxed_1895_);
    leanh::lean_dec_ref(v_as_1891_);
    v_r_1897_ = leanh::lean_box((v_res_1896_) as usize);
    return v_r_1897_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty___boxed(
    mut v_a_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: u8 = 0;
    let mut v_r_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_a_1898_);
    leanh::lean_dec(v_a_1898_);
    v_r_1900_ = leanh::lean_box((v_res_1899_) as usize);
    return v_r_1900_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(
    mut v_stx_1907_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v___y_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_1907_);
                v___x_1922_ = l_Lean_Syntax_getKind(v_stx_1907_);
                v___x_1923_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___closed__1;
                v___x_1924_ = lean_name_eq(v___x_1922_, v___x_1923_);
                leanh::lean_dec(v___x_1922_);
                if v___x_1924_ == 0 {
                    v___y_1917_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v___x_1925_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_1907_);
                    v___y_1917_ = v___x_1925_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1909_ == 0 {
                    leanh::lean_inc(v_stx_1907_);
                    v___x_1910_ = l_Lean_Syntax_getKind(v_stx_1907_);
                    v___x_1911_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4;
                    v___x_1912_ = lean_name_eq(v___x_1910_, v___x_1911_);
                    leanh::lean_dec(v___x_1910_);
                    if v___x_1912_ == 0 {
                        leanh::lean_dec(v_stx_1907_);
                        return v___x_1912_;
                    } else {
                        v___x_1913_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1914_ = l_Lean_Syntax_getArg(v_stx_1907_, v___x_1913_);
                        leanh::lean_dec(v_stx_1907_);
                        v___x_1915_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v___x_1914_);
                        leanh::lean_dec(v___x_1914_);
                        return v___x_1915_;
                    }
                } else {
                    leanh::lean_dec(v_stx_1907_);
                    return v___y_1909_;
                }
            }
            2 => {
                if v___y_1917_ == 0 {
                    leanh::lean_inc(v_stx_1907_);
                    v___x_1918_ = l_Lean_Syntax_getKind(v_stx_1907_);
                    v___x_1919_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__2;
                    v___x_1920_ = lean_name_eq(v___x_1918_, v___x_1919_);
                    leanh::lean_dec(v___x_1918_);
                    if v___x_1920_ == 0 {
                        v___y_1909_ = v___x_1920_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1921_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmpty(v_stx_1907_);
                        v___y_1909_ = v___x_1921_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_1907_);
                    return v___y_1917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock___boxed(
    mut v_stx_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1927_: u8 = 0;
    let mut v_r_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_1926_);
    v_r_1928_ = leanh::lean_box((v_res_1927_) as usize);
    return v_r_1928_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(
    mut v_fileMap_1929_: *mut leanh::LeanObject,
    mut v_hoverPos_1930_: *mut leanh::LeanObject,
    mut v_stx_1931_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_1932_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1933_: u8 = 0;
    v___x_1933_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_1929_, v_hoverPos_1930_);
    if v___x_1933_ == 0 {
        leanh::lean_dec(v_stx_1931_);
        leanh::lean_dec_ref(v_fileMap_1929_);
        return v___x_1933_;
    } else {
        let mut v___x_1934_: u8 = 0;
        let mut v___x_1935_: u8 = 0;
        v___x_1934_ = 0;
        leanh::lean_inc(v_stx_1931_);
        v___x_1935_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isEmptyTacticBlock(v_stx_1931_);
        if v___x_1935_ == 0 {
            leanh::lean_dec(v_stx_1931_);
            leanh::lean_dec_ref(v_fileMap_1929_);
            return v___x_1934_;
        } else {
            let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1938_: u8 = 0;
            leanh::lean_inc(v_stx_1931_);
            v___x_1936_ = l_Lean_Syntax_getKind(v_stx_1931_);
            v___x_1937_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_getTacticsNode_x3f___closed__4;
            v___x_1938_ = lean_name_eq(v___x_1936_, v___x_1937_);
            leanh::lean_dec(v___x_1936_);
            if v___x_1938_ == 0 {
                let mut v___x_1939_: u8 = 0;
                leanh::lean_dec(v_stx_1931_);
                v___x_1939_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isAtExpectedTacticIndentation(v_fileMap_1929_, v_hoverPos_1930_, v_leadingTokenTailPos_x3f_1932_);
                return v___x_1939_;
            } else {
                let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_fileMap_1929_);
                v___x_1940_ = leanh::lean_unsigned_to_nat(0);
                v___x_1941_ = l_Lean_Syntax_getArg(v_stx_1931_, v___x_1940_);
                v___x_1942_ = l_Lean_Syntax_getTailPos_x3f(v___x_1941_, v___x_1934_);
                leanh::lean_dec(v___x_1941_);
                if leanh::lean_obj_tag(v___x_1942_) == 1 {
                    let mut v_val_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_val_1943_ = leanh::lean_ctor_get(v___x_1942_, 0);
                    leanh::lean_inc(v_val_1943_);
                    leanh::lean_dec_ref_known(v___x_1942_, 1);
                    v___x_1944_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1945_ = l_Lean_Syntax_getArg(v_stx_1931_, v___x_1944_);
                    leanh::lean_dec(v_stx_1931_);
                    v___x_1946_ = l_Lean_Syntax_getPos_x3f(v___x_1945_, v___x_1934_);
                    leanh::lean_dec(v___x_1945_);
                    if leanh::lean_obj_tag(v___x_1946_) == 1 {
                        let mut v_val_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1948_: u8 = 0;
                        v_val_1947_ = leanh::lean_ctor_get(v___x_1946_, 0);
                        leanh::lean_inc(v_val_1947_);
                        leanh::lean_dec_ref_known(v___x_1946_, 1);
                        v___x_1948_ = lean_nat_dec_le(v_val_1943_, v_hoverPos_1930_);
                        leanh::lean_dec(v_val_1943_);
                        if v___x_1948_ == 0 {
                            leanh::lean_dec(v_val_1947_);
                            return v___x_1948_;
                        } else {
                            let mut v___x_1949_: u8 = 0;
                            v___x_1949_ = lean_nat_dec_le(v_hoverPos_1930_, v_val_1947_);
                            leanh::lean_dec(v_val_1947_);
                            return v___x_1949_;
                        }
                    } else {
                        leanh::lean_dec(v___x_1946_);
                        leanh::lean_dec(v_val_1943_);
                        return v___x_1934_;
                    }
                } else {
                    leanh::lean_dec(v___x_1942_);
                    leanh::lean_dec(v_stx_1931_);
                    return v___x_1934_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock___boxed(
    mut v_fileMap_1950_: *mut leanh::LeanObject,
    mut v_hoverPos_1951_: *mut leanh::LeanObject,
    mut v_stx_1952_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1954_: u8 = 0;
    let mut v_r_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_1950_, v_hoverPos_1951_, v_stx_1952_, v_leadingTokenTailPos_x3f_1953_);
    leanh::lean_dec(v_leadingTokenTailPos_x3f_1953_);
    leanh::lean_dec(v_hoverPos_1951_);
    v_r_1955_ = leanh::lean_box((v_res_1954_) as usize);
    return v_r_1955_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(
    mut v_fileMap_1956_: *mut leanh::LeanObject,
    mut v_hoverPos_1957_: *mut leanh::LeanObject,
    mut v_hoverFilePos_1958_: *mut leanh::LeanObject,
    mut v_stx_1959_: *mut leanh::LeanObject,
    mut v_leadingWs_1960_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_1961_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_1963_: u8 = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1968_: usize = 0;
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: u8 = 0;
    let mut v_val_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1979_ = 0;
                v___x_1980_ = l_Lean_Syntax_getPos_x3f(v_stx_1959_, v___x_1979_);
                if leanh::lean_obj_tag(v___x_1980_) == 1 {
                    v_val_1981_ = leanh::lean_ctor_get(v___x_1980_, 0);
                    leanh::lean_inc(v_val_1981_);
                    leanh::lean_dec_ref_known(v___x_1980_, 1);
                    v___x_1982_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1959_, v___x_1979_);
                    if leanh::lean_obj_tag(v___x_1982_) == 1 {
                        v_val_1983_ = leanh::lean_ctor_get(v___x_1982_, 0);
                        leanh::lean_inc(v_val_1983_);
                        leanh::lean_dec_ref_known(v___x_1982_, 1);
                        v___x_1984_ = lean_nat_sub(v_val_1981_, v_leadingWs_1960_);
                        leanh::lean_dec(v_val_1981_);
                        v___x_1985_ = lean_nat_dec_le(v___x_1984_, v_hoverPos_1957_);
                        leanh::lean_dec(v___x_1984_);
                        if v___x_1985_ == 0 {
                            leanh::lean_dec(v_val_1983_);
                            v___y_1963_ = v___x_1985_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1986_ = l_Lean_Syntax_getTrailingSize(v_stx_1959_);
                            v___x_1987_ = lean_nat_add(v_val_1983_, v___x_1986_);
                            leanh::lean_dec(v___x_1986_);
                            leanh::lean_dec(v_val_1983_);
                            v___x_1988_ = lean_nat_dec_le(v_hoverPos_1957_, v___x_1987_);
                            leanh::lean_dec(v___x_1987_);
                            v___y_1963_ = v___x_1988_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1982_);
                        leanh::lean_dec(v_val_1981_);
                        leanh::lean_dec(v_leadingWs_1960_);
                        v___x_1989_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_1956_, v_hoverPos_1957_, v_stx_1959_, v_leadingTokenTailPos_x3f_1961_);
                        leanh::lean_dec(v_leadingTokenTailPos_x3f_1961_);
                        return v___x_1989_;
                    }
                } else {
                    leanh::lean_dec(v___x_1980_);
                    leanh::lean_dec(v_leadingWs_1960_);
                    v___x_1990_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_1956_, v_hoverPos_1957_, v_stx_1959_, v_leadingTokenTailPos_x3f_1961_);
                    leanh::lean_dec(v_leadingTokenTailPos_x3f_1961_);
                    return v___x_1990_;
                }
            }
            1 => {
                if v___y_1963_ == 0 {
                    leanh::lean_dec(v_leadingTokenTailPos_x3f_1961_);
                    leanh::lean_dec(v_leadingWs_1960_);
                    leanh::lean_dec(v_stx_1959_);
                    leanh::lean_dec_ref(v_fileMap_1956_);
                    return v___y_1963_;
                } else {
                    v___x_1964_ = l_Lean_Syntax_getArgs(v_stx_1959_);
                    v___x_1965_ = leanh::lean_box(0);
                    v___x_1966_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1966_, 0, v_leadingWs_1960_);
                    leanh::lean_ctor_set(v___x_1966_, 1, v_leadingTokenTailPos_x3f_1961_);
                    v___x_1967_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1965_);
                    leanh::lean_ctor_set(v___x_1967_, 1, v___x_1966_);
                    v_sz_1968_ = lean_array_size(v___x_1964_);
                    v___x_1969_ = 0usize;
                    leanh::lean_inc_ref(v_fileMap_1956_);
                    v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_1956_, v_hoverPos_1957_, v_hoverFilePos_1958_, v___y_1963_, v___x_1964_, v_sz_1968_, v___x_1969_, v___x_1967_);
                    leanh::lean_dec_ref(v___x_1964_);
                    v_fst_1971_ = leanh::lean_ctor_get(v___x_1970_, 0);
                    leanh::lean_inc(v_fst_1971_);
                    if leanh::lean_obj_tag(v_fst_1971_) == 0 {
                        v_snd_1972_ = leanh::lean_ctor_get(v___x_1970_, 1);
                        leanh::lean_inc(v_snd_1972_);
                        leanh::lean_dec_ref(v___x_1970_);
                        v_snd_1973_ = leanh::lean_ctor_get(v_snd_1972_, 1);
                        leanh::lean_inc(v_snd_1973_);
                        leanh::lean_dec(v_snd_1972_);
                        leanh::lean_inc(v_stx_1959_);
                        leanh::lean_inc_ref(v_fileMap_1956_);
                        v___x_1974_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionInEmptyTacticBlock(v_fileMap_1956_, v_hoverPos_1957_, v_stx_1959_, v_snd_1973_);
                        leanh::lean_dec(v_snd_1973_);
                        if v___x_1974_ == 0 {
                            leanh::lean_inc(v_stx_1959_);
                            v___x_1975_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionAfterSemicolon(v_fileMap_1956_, v_hoverPos_1957_, v_stx_1959_);
                            if v___x_1975_ == 0 {
                                v___x_1976_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_isCompletionOnTacticBlockIndentation(v_fileMap_1956_, v_hoverPos_1957_, v_hoverFilePos_1958_, v_stx_1959_);
                                return v___x_1976_;
                            } else {
                                leanh::lean_dec(v_stx_1959_);
                                leanh::lean_dec_ref(v_fileMap_1956_);
                                return v___y_1963_;
                            }
                        } else {
                            leanh::lean_dec(v_stx_1959_);
                            leanh::lean_dec_ref(v_fileMap_1956_);
                            return v___y_1963_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1970_);
                        leanh::lean_dec(v_stx_1959_);
                        leanh::lean_dec_ref(v_fileMap_1956_);
                        v_val_1977_ = leanh::lean_ctor_get(v_fst_1971_, 0);
                        leanh::lean_inc(v_val_1977_);
                        leanh::lean_dec_ref_known(v_fst_1971_, 1);
                        v___x_1978_ = (leanh::lean_unbox(v_val_1977_) as u8);
                        leanh::lean_dec(v_val_1977_);
                        return v___x_1978_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(
    mut v_fileMap_1991_: *mut leanh::LeanObject,
    mut v_hoverPos_1992_: *mut leanh::LeanObject,
    mut v_hoverFilePos_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: u8,
    mut v_as_1995_: *mut leanh::LeanObject,
    mut v_sz_1996_: usize,
    mut v_i_1997_: usize,
    mut v_b_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1999_: u8 = 0;
    let mut v_snd_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v_fst_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v_a_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v_reuseFailAlloc_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut v_unused_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1999_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
                if v___x_1999_ == 0 {
                    leanh::lean_dec_ref(v_fileMap_1991_);
                    return v_b_1998_;
                } else {
                    v_snd_2000_ = leanh::lean_ctor_get(v_b_1998_, 1);
                    v_isSharedCheck_2034_ = (!leanh::lean_is_exclusive(v_b_1998_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v_unused_2035_ = leanh::lean_ctor_get(v_b_1998_, 0);
                        leanh::lean_dec(v_unused_2035_);
                        v___x_2002_ = v_b_1998_;
                        v_isShared_2003_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2000_);
                        leanh::lean_dec(v_b_1998_);
                        v___x_2002_ = leanh::lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2004_ = leanh::lean_ctor_get(v_snd_2000_, 0);
                v_snd_2005_ = leanh::lean_ctor_get(v_snd_2000_, 1);
                v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v_snd_2000_)) as u8;
                if v_isSharedCheck_2033_ == 0 {
                    v___x_2007_ = v_snd_2000_;
                    v_isShared_2008_ = v_isSharedCheck_2033_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2005_);
                    leanh::lean_inc(v_fst_2004_);
                    leanh::lean_dec(v_snd_2000_);
                    v___x_2007_ = leanh::lean_box(0);
                    v_isShared_2008_ = v_isSharedCheck_2033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2009_ = lean_array_uget_borrowed(v_as_1995_, v_i_1997_);
                leanh::lean_inc(v_snd_2005_);
                leanh::lean_inc(v_fst_2004_);
                leanh::lean_inc(v_a_2009_);
                leanh::lean_inc_ref(v_fileMap_1991_);
                v___x_2010_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_1991_, v_hoverPos_1992_, v_hoverFilePos_1993_, v_a_2009_, v_fst_2004_, v_snd_2005_);
                if v___x_2010_ == 0 {
                    leanh::lean_dec(v_fst_2004_);
                    v___x_2011_ = leanh::lean_box(0);
                    v___x_2012_ = l_Lean_Syntax_getTrailingSize(v_a_2009_);
                    v___x_2024_ = l_Lean_Syntax_getTailPos_x3f(v_a_2009_, v___x_2010_);
                    if leanh::lean_obj_tag(v___x_2024_) == 0 {
                        v___y_2014_ = v_snd_2005_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_2005_);
                        v___y_2014_ = v___x_2024_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_fileMap_1991_);
                    v___x_2025_ = leanh::lean_box((v___y_1994_) as usize);
                    v___x_2026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
                    if v_isShared_2008_ == 0 {
                        v___x_2028_ = v___x_2007_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_fst_2004_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2005_);
                        v___x_2028_ = v_reuseFailAlloc_2032_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2008_ == 0 {
                    leanh::lean_ctor_set(v___x_2007_, 1, v___y_2014_);
                    leanh::lean_ctor_set(v___x_2007_, 0, v___x_2012_);
                    v___x_2016_ = v___x_2007_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___y_2014_);
                    v___x_2016_ = v_reuseFailAlloc_2023_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2003_ == 0 {
                    leanh::lean_ctor_set(v___x_2002_, 1, v___x_2016_);
                    leanh::lean_ctor_set(v___x_2002_, 0, v___x_2011_);
                    v___x_2018_ = v___x_2002_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2016_);
                    v___x_2018_ = v_reuseFailAlloc_2022_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2019_ = 1usize;
                v___x_2020_ = lean_usize_add(v_i_1997_, v___x_2019_);
                v_i_1997_ = v___x_2020_;
                v_b_1998_ = v___x_2018_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2003_ == 0 {
                    leanh::lean_ctor_set(v___x_2002_, 1, v___x_2028_);
                    leanh::lean_ctor_set(v___x_2002_, 0, v___x_2026_);
                    v___x_2030_ = v___x_2002_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
                    v___x_2030_ = v_reuseFailAlloc_2031_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0___boxed(
    mut v_fileMap_2036_: *mut leanh::LeanObject,
    mut v_hoverPos_2037_: *mut leanh::LeanObject,
    mut v_hoverFilePos_2038_: *mut leanh::LeanObject,
    mut v___y_2039_: *mut leanh::LeanObject,
    mut v_as_2040_: *mut leanh::LeanObject,
    mut v_sz_2041_: *mut leanh::LeanObject,
    mut v_i_2042_: *mut leanh::LeanObject,
    mut v_b_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1087__boxed_2044_: u8 = 0;
    let mut v_sz_boxed_2045_: usize = 0;
    let mut v_i_boxed_2046_: usize = 0;
    let mut v_res_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_1087__boxed_2044_ = (leanh::lean_unbox(v___y_2039_) as u8);
    v_sz_boxed_2045_ = leanh::lean_unbox_usize(v_sz_2041_);
    leanh::lean_dec(v_sz_2041_);
    v_i_boxed_2046_ = leanh::lean_unbox_usize(v_i_2042_);
    leanh::lean_dec(v_i_2042_);
    v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go_spec__0(v_fileMap_2036_, v_hoverPos_2037_, v_hoverFilePos_2038_, v___y_1087__boxed_2044_, v_as_2040_, v_sz_boxed_2045_, v_i_boxed_2046_, v_b_2043_);
    leanh::lean_dec_ref(v_as_2040_);
    leanh::lean_dec_ref(v_hoverFilePos_2038_);
    leanh::lean_dec(v_hoverPos_2037_);
    return v_res_2047_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go___boxed(
    mut v_fileMap_2048_: *mut leanh::LeanObject,
    mut v_hoverPos_2049_: *mut leanh::LeanObject,
    mut v_hoverFilePos_2050_: *mut leanh::LeanObject,
    mut v_stx_2051_: *mut leanh::LeanObject,
    mut v_leadingWs_2052_: *mut leanh::LeanObject,
    mut v_leadingTokenTailPos_x3f_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2054_: u8 = 0;
    let mut v_r_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_2048_, v_hoverPos_2049_, v_hoverFilePos_2050_, v_stx_2051_, v_leadingWs_2052_, v_leadingTokenTailPos_x3f_2053_);
    leanh::lean_dec_ref(v_hoverFilePos_2050_);
    leanh::lean_dec(v_hoverPos_2049_);
    v_r_2055_ = leanh::lean_box((v_res_2054_) as usize);
    return v_r_2055_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(
    mut v_fileMap_2056_: *mut leanh::LeanObject,
    mut v_hoverPos_2057_: *mut leanh::LeanObject,
    mut v_cmdStx_2058_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_hoverFilePos_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    leanh::lean_inc_ref(v_fileMap_2056_);
    v_hoverFilePos_2059_ = l_Lean_FileMap_toPosition(v_fileMap_2056_, v_hoverPos_2057_);
    v___x_2060_ = leanh::lean_unsigned_to_nat(0);
    v___x_2061_ = leanh::lean_box(0);
    v___x_2062_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion_go(v_fileMap_2056_, v_hoverPos_2057_, v_hoverFilePos_2059_, v_cmdStx_2058_, v___x_2060_, v___x_2061_);
    leanh::lean_dec_ref(v_hoverFilePos_2059_);
    return v___x_2062_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion___boxed(
    mut v_fileMap_2063_: *mut leanh::LeanObject,
    mut v_hoverPos_2064_: *mut leanh::LeanObject,
    mut v_cmdStx_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2066_: u8 = 0;
    let mut v_r_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_2063_, v_hoverPos_2064_, v_cmdStx_2065_);
    leanh::lean_dec(v_hoverPos_2064_);
    v_r_2067_ = leanh::lean_box((v_res_2066_) as usize);
    return v_r_2067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(
    mut v_as_2073_: *mut leanh::LeanObject,
    mut v_sz_2074_: usize,
    mut v_i_2075_: usize,
    mut v_b_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: usize = 0;
    let mut v___x_2085_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2077_ = lean_usize_dec_lt(v_i_2075_, v_sz_2074_);
                if v___x_2077_ == 0 {
                    leanh::lean_inc_ref(v_b_2076_);
                    return v_b_2076_;
                } else {
                    v___x_2078_ = leanh::lean_box(0);
                    v_a_2079_ = lean_array_uget_borrowed(v_as_2073_, v_i_2075_);
                    v___x_2080_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_a_2079_);
                    if leanh::lean_obj_tag(v___x_2080_) == 1 {
                        v___x_2081_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2081_, 0, v___x_2080_);
                        v___x_2082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                        leanh::lean_ctor_set(v___x_2082_, 1, v___x_2078_);
                        return v___x_2082_;
                    } else {
                        leanh::lean_dec(v___x_2080_);
                        v___x_2083_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0;
                        v___x_2084_ = 1usize;
                        v___x_2085_ = lean_usize_add(v_i_2075_, v___x_2084_);
                        v_i_2075_ = v___x_2085_;
                        v_b_2076_ = v___x_2083_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(
    mut v_as_2087_: *mut leanh::LeanObject,
    mut v_sz_2088_: usize,
    mut v_i_2089_: usize,
    mut v_b_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: usize = 0;
    let mut v___x_2099_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2091_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
                if v___x_2091_ == 0 {
                    leanh::lean_inc_ref(v_b_2090_);
                    return v_b_2090_;
                } else {
                    v___x_2092_ = leanh::lean_box(0);
                    v_a_2093_ = lean_array_uget_borrowed(v_as_2087_, v_i_2089_);
                    leanh::lean_inc(v_a_2093_);
                    v___x_2094_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_a_2093_);
                    if leanh::lean_obj_tag(v___x_2094_) == 1 {
                        v___x_2095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2095_, 0, v___x_2094_);
                        v___x_2096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2096_, 0, v___x_2095_);
                        leanh::lean_ctor_set(v___x_2096_, 1, v___x_2092_);
                        return v___x_2096_;
                    } else {
                        leanh::lean_dec(v___x_2094_);
                        v___x_2097_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0;
                        v___x_2098_ = 1usize;
                        v___x_2099_ = lean_usize_add(v_i_2089_, v___x_2098_);
                        v_i_2089_ = v___x_2099_;
                        v_b_2090_ = v___x_2097_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(
    mut v_x_2101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2101_) == 0 {
        let mut v_cs_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2105_: usize = 0;
        let mut v___x_2106_: usize = 0;
        let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_2102_ = leanh::lean_ctor_get(v_x_2101_, 0);
        v___x_2103_ = leanh::lean_box(0);
        v___x_2104_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0;
        v_sz_2105_ = lean_array_size(v_cs_2102_);
        v___x_2106_ = 0usize;
        v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_cs_2102_, v_sz_2105_, v___x_2106_, v___x_2104_);
        v_fst_2108_ = leanh::lean_ctor_get(v___x_2107_, 0);
        leanh::lean_inc(v_fst_2108_);
        leanh::lean_dec_ref(v___x_2107_);
        if leanh::lean_obj_tag(v_fst_2108_) == 0 {
            return v___x_2103_;
        } else {
            let mut v_val_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2109_ = leanh::lean_ctor_get(v_fst_2108_, 0);
            leanh::lean_inc(v_val_2109_);
            leanh::lean_dec_ref_known(v_fst_2108_, 1);
            return v_val_2109_;
        }
    } else {
        let mut v_vs_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2113_: usize = 0;
        let mut v___x_2114_: usize = 0;
        let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_2110_ = leanh::lean_ctor_get(v_x_2101_, 0);
        v___x_2111_ = leanh::lean_box(0);
        v___x_2112_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0;
        v_sz_2113_ = lean_array_size(v_vs_2110_);
        v___x_2114_ = 0usize;
        v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_vs_2110_, v_sz_2113_, v___x_2114_, v___x_2112_);
        v_fst_2116_ = leanh::lean_ctor_get(v___x_2115_, 0);
        leanh::lean_inc(v_fst_2116_);
        leanh::lean_dec_ref(v___x_2115_);
        if leanh::lean_obj_tag(v_fst_2116_) == 0 {
            return v___x_2111_;
        } else {
            let mut v_val_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2117_ = leanh::lean_ctor_get(v_fst_2116_, 0);
            leanh::lean_inc(v_val_2117_);
            leanh::lean_dec_ref_known(v_fst_2116_, 1);
            return v_val_2117_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(
    mut v_t_2118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_2119_ = leanh::lean_ctor_get(v_t_2118_, 0);
    v_tail_2120_ = leanh::lean_ctor_get(v_t_2118_, 1);
    v___x_2121_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_root_2119_);
    if leanh::lean_obj_tag(v___x_2121_) == 0 {
        let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2123_: usize = 0;
        let mut v___x_2124_: usize = 0;
        let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2122_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___closed__0;
        v_sz_2123_ = lean_array_size(v_tail_2120_);
        v___x_2124_ = 0usize;
        v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_tail_2120_, v_sz_2123_, v___x_2124_, v___x_2122_);
        v_fst_2126_ = leanh::lean_ctor_get(v___x_2125_, 0);
        leanh::lean_inc(v_fst_2126_);
        leanh::lean_dec_ref(v___x_2125_);
        if leanh::lean_obj_tag(v_fst_2126_) == 0 {
            return v___x_2121_;
        } else {
            let mut v_val_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2127_ = leanh::lean_ctor_get(v_fst_2126_, 0);
            leanh::lean_inc(v_val_2127_);
            leanh::lean_dec_ref_known(v_fst_2126_, 1);
            return v_val_2127_;
        }
    } else {
        return v___x_2121_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(
    mut v_i_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_t_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_2128_) {
                0 => {
                    v_i_2129_ = leanh::lean_ctor_get(v_i_2128_, 0);
                    leanh::lean_inc_ref(v_i_2129_);
                    if leanh::lean_obj_tag(v_i_2129_) == 0 {
                        leanh::lean_dec_ref_known(v_i_2128_, 2);
                        v_info_2130_ = leanh::lean_ctor_get(v_i_2129_, 0);
                        v_isSharedCheck_2140_ = (!leanh::lean_is_exclusive(v_i_2129_)) as u8;
                        if v_isSharedCheck_2140_ == 0 {
                            v___x_2132_ = v_i_2129_;
                            v_isShared_2133_ = v_isSharedCheck_2140_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_info_2130_);
                            leanh::lean_dec(v_i_2129_);
                            v___x_2132_ = leanh::lean_box(0);
                            v_isShared_2133_ = v_isSharedCheck_2140_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_i_2129_);
                        v_t_2141_ = leanh::lean_ctor_get(v_i_2128_, 1);
                        leanh::lean_inc_ref(v_t_2141_);
                        leanh::lean_dec_ref_known(v_i_2128_, 2);
                        v_i_2128_ = v_t_2141_;
                        state = 0;
                        continue;
                    }
                }
                1 => {
                    v_children_2143_ = leanh::lean_ctor_get(v_i_2128_, 1);
                    leanh::lean_inc_ref(v_children_2143_);
                    leanh::lean_dec_ref_known(v_i_2128_, 2);
                    v___x_2144_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_children_2143_);
                    leanh::lean_dec_ref(v_children_2143_);
                    return v___x_2144_;
                }
                _ => {
                    leanh::lean_dec_ref_known(v_i_2128_, 1);
                    v___x_2145_ = leanh::lean_box(0);
                    return v___x_2145_;
                }
            },
            1 => {
                v___x_2134_ = leanh::lean_box(0);
                v___x_2135_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go___closed__0;
                v___x_2136_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2136_, 0, v_info_2130_);
                leanh::lean_ctor_set(v___x_2136_, 1, v___x_2134_);
                leanh::lean_ctor_set(v___x_2136_, 2, v___x_2135_);
                if v_isShared_2133_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2132_, 1);
                    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2136_);
                    v___x_2138_ = v___x_2132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
                    v___x_2138_ = v_reuseFailAlloc_2139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0___boxed(
    mut v_t_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0(v_t_2146_);
    leanh::lean_dec_ref(v_t_2146_);
    return v_res_2147_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1___boxed(
    mut v_as_2148_: *mut leanh::LeanObject,
    mut v_sz_2149_: *mut leanh::LeanObject,
    mut v_i_2150_: *mut leanh::LeanObject,
    mut v_b_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2152_: usize = 0;
    let mut v_i_boxed_2153_: usize = 0;
    let mut v_res_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2152_ = leanh::lean_unbox_usize(v_sz_2149_);
    leanh::lean_dec(v_sz_2149_);
    v_i_boxed_2153_ = leanh::lean_unbox_usize(v_i_2150_);
    leanh::lean_dec(v_i_2150_);
    v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__1(v_as_2148_, v_sz_boxed_2152_, v_i_boxed_2153_, v_b_2151_);
    leanh::lean_dec_ref(v_b_2151_);
    leanh::lean_dec_ref(v_as_2148_);
    return v_res_2154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1___boxed(
    mut v_as_2155_: *mut leanh::LeanObject,
    mut v_sz_2156_: *mut leanh::LeanObject,
    mut v_i_2157_: *mut leanh::LeanObject,
    mut v_b_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2159_: usize = 0;
    let mut v_i_boxed_2160_: usize = 0;
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2159_ = leanh::lean_unbox_usize(v_sz_2156_);
    leanh::lean_dec(v_sz_2156_);
    v_i_boxed_2160_ = leanh::lean_unbox_usize(v_i_2157_);
    leanh::lean_dec(v_i_2157_);
    v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0_spec__1(v_as_2155_, v_sz_boxed_2159_, v_i_boxed_2160_, v_b_2158_);
    leanh::lean_dec_ref(v_b_2158_);
    leanh::lean_dec_ref(v_as_2155_);
    return v_res_2161_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0___boxed(
    mut v_x_2162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go_spec__0_spec__0(v_x_2162_);
    leanh::lean_dec_ref(v_x_2162_);
    return v_res_2163_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f(
    mut v_i_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_i_2164_);
    return v___x_2165_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(
    mut v_fileMap_2168_: *mut leanh::LeanObject,
    mut v_hoverPos_2169_: *mut leanh::LeanObject,
    mut v_cmdStx_2170_: *mut leanh::LeanObject,
    mut v_infoTree_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2172_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findOutermostContextInfo_x3f_go(v_infoTree_2171_);
                if leanh::lean_obj_tag(v___x_2172_) == 0 {
                    leanh::lean_dec(v_cmdStx_2170_);
                    leanh::lean_dec_ref(v_fileMap_2168_);
                    v___x_2173_ = leanh::lean_box(0);
                    return v___x_2173_;
                } else {
                    v_val_2174_ = leanh::lean_ctor_get(v___x_2172_, 0);
                    v_isSharedCheck_2186_ = (!leanh::lean_is_exclusive(v___x_2172_)) as u8;
                    if v_isSharedCheck_2186_ == 0 {
                        v___x_2176_ = v___x_2172_;
                        v_isShared_2177_ = v_isSharedCheck_2186_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2174_);
                        leanh::lean_dec(v___x_2172_);
                        v___x_2176_ = leanh::lean_box(0);
                        v_isShared_2177_ = v_isSharedCheck_2186_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2178_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticTacticCompletion(v_fileMap_2168_, v_hoverPos_2169_, v_cmdStx_2170_);
                if v___x_2178_ == 0 {
                    leanh::lean_del_object(v___x_2176_);
                    leanh::lean_dec(v_val_2174_);
                    v___x_2179_ = leanh::lean_box(0);
                    return v___x_2179_;
                } else {
                    v___x_2180_ = leanh::lean_box(0);
                    v___x_2181_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___closed__0;
                    v___x_2182_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2180_);
                    leanh::lean_ctor_set(v___x_2182_, 1, v_val_2174_);
                    leanh::lean_ctor_set(v___x_2182_, 2, v___x_2181_);
                    if v_isShared_2177_ == 0 {
                        leanh::lean_ctor_set(v___x_2176_, 0, v___x_2182_);
                        v___x_2184_ = v___x_2176_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
                        v___x_2184_ = v_reuseFailAlloc_2185_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f___boxed(
    mut v_fileMap_2187_: *mut leanh::LeanObject,
    mut v_hoverPos_2188_: *mut leanh::LeanObject,
    mut v_cmdStx_2189_: *mut leanh::LeanObject,
    mut v_infoTree_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2191_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_2187_, v_hoverPos_2188_, v_cmdStx_2189_, v_infoTree_2190_);
    leanh::lean_dec(v_hoverPos_2188_);
    return v_res_2191_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(
    mut v_msg_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = l_Lean_instInhabitedExpr;
    v___x_2194_ = lean_panic_fn_borrowed(v___x_2193_, v_msg_2192_);
    return v___x_2194_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(
    mut v_hoverPos_2195_: *mut leanh::LeanObject,
    mut v_i_2196_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_Elab_Info_pos_x3f(v_i_2196_);
    if leanh::lean_obj_tag(v___x_2197_) == 1 {
        let mut v_val_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2198_ = leanh::lean_ctor_get(v___x_2197_, 0);
        leanh::lean_inc(v_val_2198_);
        leanh::lean_dec_ref_known(v___x_2197_, 1);
        v___x_2199_ = l_Lean_Elab_Info_tailPos_x3f(v_i_2196_);
        if leanh::lean_obj_tag(v___x_2199_) == 1 {
            if leanh::lean_obj_tag(v_i_2196_) == 1 {
                let mut v_i_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_expectedType_x3f_2201_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                v_i_2200_ = leanh::lean_ctor_get(v_i_2196_, 0);
                v_expectedType_x3f_2201_ = leanh::lean_ctor_get(v_i_2200_, 2);
                if leanh::lean_obj_tag(v_expectedType_x3f_2201_) == 0 {
                    let mut v___x_2202_: u8 = 0;
                    leanh::lean_dec_ref_known(v___x_2199_, 1);
                    leanh::lean_dec(v_val_2198_);
                    v___x_2202_ = 0;
                    return v___x_2202_;
                } else {
                    let mut v_val_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2204_: u8 = 0;
                    v_val_2203_ = leanh::lean_ctor_get(v___x_2199_, 0);
                    leanh::lean_inc(v_val_2203_);
                    leanh::lean_dec_ref_known(v___x_2199_, 1);
                    v___x_2204_ = lean_nat_dec_le(v_val_2198_, v_hoverPos_2195_);
                    leanh::lean_dec(v_val_2198_);
                    if v___x_2204_ == 0 {
                        leanh::lean_dec(v_val_2203_);
                        return v___x_2204_;
                    } else {
                        let mut v___x_2205_: u8 = 0;
                        v___x_2205_ = lean_nat_dec_le(v_hoverPos_2195_, v_val_2203_);
                        leanh::lean_dec(v_val_2203_);
                        return v___x_2205_;
                    }
                }
            } else {
                let mut v___x_2206_: u8 = 0;
                leanh::lean_dec_ref_known(v___x_2199_, 1);
                leanh::lean_dec(v_val_2198_);
                v___x_2206_ = 0;
                return v___x_2206_;
            }
        } else {
            let mut v___x_2207_: u8 = 0;
            leanh::lean_dec(v___x_2199_);
            leanh::lean_dec(v_val_2198_);
            v___x_2207_ = 0;
            return v___x_2207_;
        }
    } else {
        let mut v___x_2208_: u8 = 0;
        leanh::lean_dec(v___x_2197_);
        v___x_2208_ = 0;
        return v___x_2208_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed(
    mut v_hoverPos_2209_: *mut leanh::LeanObject,
    mut v_i_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2211_: u8 = 0;
    let mut v_r_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2211_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0(v_hoverPos_2209_, v_i_2210_);
    leanh::lean_dec_ref(v_i_2210_);
    leanh::lean_dec(v_hoverPos_2209_);
    v_r_2212_ = leanh::lean_box((v_res_2211_) as usize);
    return v_r_2212_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(
    mut v_infoTree_2213_: *mut leanh::LeanObject,
    mut v_hoverPos_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v_fst_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___y_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2215_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_2215_, 0, v_hoverPos_2214_);
                v___x_2216_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_2215_, v_infoTree_2213_);
                if leanh::lean_obj_tag(v___x_2216_) == 0 {
                    v___x_2217_ = leanh::lean_box(0);
                    return v___x_2217_;
                } else {
                    v_val_2218_ = leanh::lean_ctor_get(v___x_2216_, 0);
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2216_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2220_ = v___x_2216_;
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2218_);
                        leanh::lean_dec(v___x_2216_);
                        v___x_2220_ = leanh::lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2222_ = leanh::lean_ctor_get(v_val_2218_, 0);
                v_snd_2223_ = leanh::lean_ctor_get(v_val_2218_, 1);
                v_isSharedCheck_2241_ = (!leanh::lean_is_exclusive(v_val_2218_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v___x_2225_ = v_val_2218_;
                    v_isShared_2226_ = v_isSharedCheck_2241_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2223_);
                    leanh::lean_inc(v_fst_2222_);
                    leanh::lean_dec(v_val_2218_);
                    v___x_2225_ = leanh::lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_snd_2223_) == 1 {
                    v_i_2235_ = leanh::lean_ctor_get(v_snd_2223_, 0);
                    leanh::lean_inc_ref(v_i_2235_);
                    leanh::lean_dec_ref_known(v_snd_2223_, 1);
                    v_expectedType_x3f_2236_ = leanh::lean_ctor_get(v_i_2235_, 2);
                    leanh::lean_inc(v_expectedType_x3f_2236_);
                    leanh::lean_dec_ref(v_i_2235_);
                    if leanh::lean_obj_tag(v_expectedType_x3f_2236_) == 0 {
                        v___x_2237_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4_once), _init_l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f___closed__4);
                        v___x_2238_ = l_panic___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt_spec__0(v___x_2237_);
                        v___y_2228_ = v___x_2238_;
                        state = 3;
                        continue;
                    } else {
                        v_val_2239_ = leanh::lean_ctor_get(v_expectedType_x3f_2236_, 0);
                        leanh::lean_inc(v_val_2239_);
                        leanh::lean_dec_ref_known(v_expectedType_x3f_2236_, 1);
                        v___y_2228_ = v_val_2239_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2225_);
                    leanh::lean_dec(v_snd_2223_);
                    leanh::lean_dec(v_fst_2222_);
                    leanh::lean_del_object(v___x_2220_);
                    v___x_2240_ = leanh::lean_box(0);
                    return v___x_2240_;
                }
            }
            3 => {
                if v_isShared_2226_ == 0 {
                    leanh::lean_ctor_set(v___x_2225_, 1, v___y_2228_);
                    v___x_2230_ = v___x_2225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_fst_2222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___y_2228_);
                    v___x_2230_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2221_ == 0 {
                    leanh::lean_ctor_set(v___x_2220_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2220_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
                    v___x_2232_ = v_reuseFailAlloc_2233_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(
    mut v_f_2243_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2244_: *mut leanh::LeanObject,
    mut v_acc_2245_: *mut leanh::LeanObject,
    mut v_stx_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastToken_x3f_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2264_: usize = 0;
    let mut v___x_2265_: usize = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2247_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__0;
                v___f_2248_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__1;
                v___f_2249_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__2;
                v___f_2250_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__3;
                v___f_2251_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__4;
                v___f_2252_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__5;
                v___f_2253_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findBest_x3f_spec__0_spec__0___redArg___closed__6;
                v___x_2254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2254_, 0, v___f_2247_);
                leanh::lean_ctor_set(v___x_2254_, 1, v___f_2248_);
                v___x_2255_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2255_, 0, v___x_2254_);
                leanh::lean_ctor_set(v___x_2255_, 1, v___f_2249_);
                leanh::lean_ctor_set(v___x_2255_, 2, v___f_2250_);
                leanh::lean_ctor_set(v___x_2255_, 3, v___f_2251_);
                leanh::lean_ctor_set(v___x_2255_, 4, v___f_2252_);
                v___x_2256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2256_, 0, v___x_2255_);
                leanh::lean_ctor_set(v___x_2256_, 1, v___f_2253_);
                leanh::lean_inc(v_f_2243_);
                leanh::lean_inc(v_stx_2246_);
                leanh::lean_inc(v_leadingToken_x3f_2244_);
                v_acc_2257_ = leanh::lean_apply_3(
                    v_f_2243_,
                    v_acc_2245_,
                    v_leadingToken_x3f_2244_,
                    v_stx_2246_,
                );
                match leanh::lean_obj_tag(v_stx_2246_) {
                    0 => {
                        leanh::lean_dec_ref_known(v___x_2256_, 2);
                        leanh::lean_dec(v_leadingToken_x3f_2244_);
                        leanh::lean_dec(v_f_2243_);
                        v___x_2258_ = leanh::lean_box(0);
                        v___x_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
                        leanh::lean_ctor_set(v___x_2259_, 1, v_acc_2257_);
                        return v___x_2259_;
                    }
                    1 => {
                        v_args_2260_ = leanh::lean_ctor_get(v_stx_2246_, 2);
                        leanh::lean_inc_ref(v_args_2260_);
                        leanh::lean_dec_ref_known(v_stx_2246_, 3);
                        v___f_2261_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0 as *mut core::ffi::c_void, 5, 2);
                        leanh::lean_closure_set(v___f_2261_, 0, v_f_2243_);
                        leanh::lean_closure_set(v___f_2261_, 1, v_leadingToken_x3f_2244_);
                        v_lastToken_x3f_2262_ = leanh::lean_box(0);
                        v___x_2263_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2263_, 0, v_acc_2257_);
                        leanh::lean_ctor_set(v___x_2263_, 1, v_lastToken_x3f_2262_);
                        v_sz_2264_ = lean_array_size(v_args_2260_);
                        v___x_2265_ = 0usize;
                        v___x_2266_ =
                            l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2256_,
                                v_args_2260_,
                                v___f_2261_,
                                v_sz_2264_,
                                v___x_2265_,
                                v___x_2263_,
                            );
                        v_fst_2267_ = leanh::lean_ctor_get(v___x_2266_, 0);
                        v_snd_2268_ = leanh::lean_ctor_get(v___x_2266_, 1);
                        v_isSharedCheck_2275_ =
                            (!leanh::lean_is_exclusive(v___x_2266_)) as u8;
                        if v_isSharedCheck_2275_ == 0 {
                            v___x_2270_ = v___x_2266_;
                            v_isShared_2271_ = v_isSharedCheck_2275_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2268_);
                            leanh::lean_inc(v_fst_2267_);
                            leanh::lean_dec(v___x_2266_);
                            v___x_2270_ = leanh::lean_box(0);
                            v_isShared_2271_ = v_isSharedCheck_2275_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref_known(v___x_2256_, 2);
                        leanh::lean_dec(v_leadingToken_x3f_2244_);
                        leanh::lean_dec(v_f_2243_);
                        v___x_2276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2276_, 0, v_stx_2246_);
                        v___x_2277_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
                        leanh::lean_ctor_set(v___x_2277_, 1, v_acc_2257_);
                        return v___x_2277_;
                    }
                }
            }
            1 => {
                if v_isShared_2271_ == 0 {
                    leanh::lean_ctor_set(v___x_2270_, 1, v_fst_2267_);
                    leanh::lean_ctor_set(v___x_2270_, 0, v_snd_2268_);
                    v___x_2273_ = v___x_2270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_snd_2268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_fst_2267_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg___lam__0(
    mut v_f_2278_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
    mut v_x_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2288_ = leanh::lean_ctor_get(v___y_2282_, 0);
                leanh::lean_inc(v_fst_2288_);
                v_snd_2289_ = leanh::lean_ctor_get(v___y_2282_, 1);
                leanh::lean_inc(v_snd_2289_);
                leanh::lean_dec_ref(v___y_2282_);
                if leanh::lean_obj_tag(v_snd_2289_) == 0 {
                    v___y_2291_ = v_leadingToken_x3f_2279_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_leadingToken_x3f_2279_);
                    leanh::lean_inc_ref(v_snd_2289_);
                    v___y_2291_ = v_snd_2289_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2286_, 0, v___y_2284_);
                leanh::lean_ctor_set(v___x_2286_, 1, v___y_2285_);
                v___x_2287_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2287_, 0, v___x_2286_);
                return v___x_2287_;
            }
            2 => {
                v___x_2292_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_2278_, v___y_2291_, v_fst_2288_, v_a_2280_);
                v_fst_2293_ = leanh::lean_ctor_get(v___x_2292_, 0);
                leanh::lean_inc(v_fst_2293_);
                if leanh::lean_obj_tag(v_fst_2293_) == 0 {
                    v_snd_2294_ = leanh::lean_ctor_get(v___x_2292_, 1);
                    leanh::lean_inc(v_snd_2294_);
                    leanh::lean_dec_ref(v___x_2292_);
                    v___y_2284_ = v_snd_2294_;
                    v___y_2285_ = v_snd_2289_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2289_);
                    v_snd_2295_ = leanh::lean_ctor_get(v___x_2292_, 1);
                    leanh::lean_inc(v_snd_2295_);
                    leanh::lean_dec_ref(v___x_2292_);
                    v___y_2284_ = v_snd_2295_;
                    v___y_2285_ = v_fst_2293_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(
    mut v_00_u03b1_2296_: *mut leanh::LeanObject,
    mut v_f_2297_: *mut leanh::LeanObject,
    mut v_inst_2298_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2299_: *mut leanh::LeanObject,
    mut v_acc_2300_: *mut leanh::LeanObject,
    mut v_stx_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_2297_, v_leadingToken_x3f_2299_, v_acc_2300_, v_stx_2301_);
    return v___x_2302_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___boxed(
    mut v_00_u03b1_2303_: *mut leanh::LeanObject,
    mut v_f_2304_: *mut leanh::LeanObject,
    mut v_inst_2305_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2306_: *mut leanh::LeanObject,
    mut v_acc_2307_: *mut leanh::LeanObject,
    mut v_stx_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go(v_00_u03b1_2303_, v_f_2304_, v_inst_2305_, v_leadingToken_x3f_2306_, v_acc_2307_, v_stx_2308_);
    leanh::lean_dec(v_inst_2305_);
    return v_res_2309_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(
    mut v_f_2310_: *mut leanh::LeanObject,
    mut v_init_2311_: *mut leanh::LeanObject,
    mut v_stx_2312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = leanh::lean_box(0);
    v___x_2314_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken_go___redArg(v_f_2310_, v___x_2313_, v_init_2311_, v_stx_2312_);
    v_snd_2315_ = leanh::lean_ctor_get(v___x_2314_, 1);
    leanh::lean_inc(v_snd_2315_);
    leanh::lean_dec_ref(v___x_2314_);
    return v_snd_2315_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(
    mut v_00_u03b1_2316_: *mut leanh::LeanObject,
    mut v_inst_2317_: *mut leanh::LeanObject,
    mut v_f_2318_: *mut leanh::LeanObject,
    mut v_init_2319_: *mut leanh::LeanObject,
    mut v_stx_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v_f_2318_, v_init_2319_, v_stx_2320_);
    return v___x_2321_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___boxed(
    mut v_00_u03b1_2322_: *mut leanh::LeanObject,
    mut v_inst_2323_: *mut leanh::LeanObject,
    mut v_f_2324_: *mut leanh::LeanObject,
    mut v_init_2325_: *mut leanh::LeanObject,
    mut v_stx_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2327_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken(v_00_u03b1_2322_, v_inst_2323_, v_f_2324_, v_init_2325_, v_stx_2326_);
    leanh::lean_dec(v_inst_2323_);
    return v_res_2327_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(
    mut v_p_2328_: *mut leanh::LeanObject,
    mut v_foundStx_x3f_2329_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2330_: *mut leanh::LeanObject,
    mut v_stx_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_foundStx_x3f_2329_) == 0 {
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: u8 = 0;
        leanh::lean_inc(v_stx_2331_);
        v___x_2332_ = leanh::lean_apply_2(v_p_2328_, v_leadingToken_x3f_2330_, v_stx_2331_);
        v___x_2333_ = (leanh::lean_unbox(v___x_2332_) as u8);
        if v___x_2333_ == 0 {
            leanh::lean_dec(v_stx_2331_);
            return v_foundStx_x3f_2329_;
        } else {
            let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2334_, 0, v_stx_2331_);
            return v___x_2334_;
        }
    } else {
        leanh::lean_dec(v_stx_2331_);
        leanh::lean_dec(v_leadingToken_x3f_2330_);
        leanh::lean_dec_ref(v_p_2328_);
        leanh::lean_inc_ref(v_foundStx_x3f_2329_);
        return v_foundStx_x3f_2329_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed(
    mut v_p_2335_: *mut leanh::LeanObject,
    mut v_foundStx_x3f_2336_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2337_: *mut leanh::LeanObject,
    mut v_stx_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2339_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0(v_p_2335_, v_foundStx_x3f_2336_, v_leadingToken_x3f_2337_, v_stx_2338_);
    leanh::lean_dec(v_foundStx_x3f_2336_);
    return v_res_2339_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(
    mut v_p_2340_: *mut leanh::LeanObject,
    mut v_stx_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2342_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_2342_, 0, v_p_2340_);
    v___x_2343_ = leanh::lean_box(0);
    v___x_2344_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_foldWithLeadingToken___redArg(v___f_2342_, v___x_2343_, v_stx_2341_);
    return v___x_2344_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(
    mut v___y_2345_: u8,
    mut v_hoverPos_2346_: *mut leanh::LeanObject,
    mut v_as_2347_: *mut leanh::LeanObject,
    mut v_i_2348_: usize,
    mut v_stop_2349_: usize,
) -> u8 {
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___y_2357_: u8 = 0;
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: usize = 0;
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: u8 = 0;
    let mut v___x_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2350_ = lean_usize_dec_eq(v_i_2348_, v_stop_2349_);
                if v___x_2350_ == 0 {
                    v___x_2351_ = lean_array_uget_borrowed(v_as_2347_, v_i_2348_);
                    v_fst_2352_ = leanh::lean_ctor_get(v___x_2351_, 0);
                    v_snd_2353_ = leanh::lean_ctor_get(v___x_2351_, 1);
                    v___x_2354_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2355_ = 1;
                    v___x_2361_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2362_ = lean_nat_mod(v_snd_2353_, v___x_2361_);
                    v___x_2363_ = lean_nat_dec_eq(v___x_2362_, v___x_2354_);
                    leanh::lean_dec(v___x_2362_);
                    if v___x_2363_ == 0 {
                        v___x_2364_ = l_Lean_Syntax_isAtom(v_fst_2352_);
                        if v___x_2364_ == 0 {
                            v___y_2357_ = v___y_2345_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_2363_ == 0 {
                                v___x_2365_ =
                                    l_Lean_Syntax_getTailPos_x3f(v_fst_2352_, v___x_2363_);
                                if leanh::lean_obj_tag(v___x_2365_) == 1 {
                                    v_val_2366_ = leanh::lean_ctor_get(v___x_2365_, 0);
                                    leanh::lean_inc(v_val_2366_);
                                    leanh::lean_dec_ref_known(v___x_2365_, 1);
                                    v___x_2367_ = lean_nat_dec_le(v_val_2366_, v_hoverPos_2346_);
                                    if v___x_2367_ == 0 {
                                        leanh::lean_dec(v_val_2366_);
                                        v___y_2357_ = v___x_2367_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2368_ = l_Lean_Syntax_getTrailingSize(v_fst_2352_);
                                        v___x_2369_ = lean_nat_add(v_val_2366_, v___x_2368_);
                                        leanh::lean_dec(v___x_2368_);
                                        leanh::lean_dec(v_val_2366_);
                                        v___x_2370_ =
                                            lean_nat_dec_le(v_hoverPos_2346_, v___x_2369_);
                                        leanh::lean_dec(v___x_2369_);
                                        v___y_2357_ = v___x_2370_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2365_);
                                    v___y_2357_ = v___x_2363_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_2357_ = v___y_2345_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___y_2357_ = v___y_2345_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2371_ = 0;
                    return v___x_2371_;
                }
            }
            1 => {
                if v___y_2357_ == 0 {
                    v___x_2358_ = 1usize;
                    v___x_2359_ = lean_usize_add(v_i_2348_, v___x_2358_);
                    v_i_2348_ = v___x_2359_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2355_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0___boxed(
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v_hoverPos_2373_: *mut leanh::LeanObject,
    mut v_as_2374_: *mut leanh::LeanObject,
    mut v_i_2375_: *mut leanh::LeanObject,
    mut v_stop_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2411__boxed_2377_: u8 = 0;
    let mut v_i_boxed_2378_: usize = 0;
    let mut v_stop_boxed_2379_: usize = 0;
    let mut v_res_2380_: u8 = 0;
    let mut v_r_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_2411__boxed_2377_ = (leanh::lean_unbox(v___y_2372_) as u8);
    v_i_boxed_2378_ = leanh::lean_unbox_usize(v_i_2375_);
    leanh::lean_dec(v_i_2375_);
    v_stop_boxed_2379_ = leanh::lean_unbox_usize(v_stop_2376_);
    leanh::lean_dec(v_stop_2376_);
    v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_2411__boxed_2377_, v_hoverPos_2373_, v_as_2374_, v_i_boxed_2378_, v_stop_boxed_2379_);
    leanh::lean_dec_ref(v_as_2374_);
    leanh::lean_dec(v_hoverPos_2373_);
    v_r_2381_ = leanh::lean_box((v_res_2380_) as usize);
    return v_r_2381_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(
    mut v___x_2388_: u8,
    mut v_isCursorOnWhitespace_2389_: u8,
    mut v_isCursorInProperWhitespace_2390_: u8,
    mut v_fileMap_2391_: *mut leanh::LeanObject,
    mut v_hoverFilePos_2392_: *mut leanh::LeanObject,
    mut v_hoverPos_2393_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2394_: *mut leanh::LeanObject,
    mut v_stx_2395_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_2397_: u8 = 0;
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCursorInBlock_2403_: u8 = 0;
    let mut v_val_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldsAndSeps_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2414_: u8 = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: usize = 0;
    let mut v___x_2420_: u8 = 0;
    let mut v___y_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v_outerBounds_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_leadingToken_x3f_2394_) == 1 {
                    v_val_2404_ = leanh::lean_ctor_get(v_leadingToken_x3f_2394_, 0);
                    leanh::lean_inc(v_stx_2395_);
                    v___x_2405_ = l_Lean_Syntax_getKind(v_stx_2395_);
                    v___x_2406_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___closed__1;
                    v___x_2407_ = lean_name_eq(v___x_2405_, v___x_2406_);
                    leanh::lean_dec(v___x_2405_);
                    if v___x_2407_ == 0 {
                        leanh::lean_dec(v_stx_2395_);
                        leanh::lean_dec_ref(v_fileMap_2391_);
                        return v___x_2388_;
                    } else {
                        v___x_2408_ =
                            l_Lean_Syntax_getTailPos_x3f(v_val_2404_, v_isCursorOnWhitespace_2389_);
                        if leanh::lean_obj_tag(v___x_2408_) == 1 {
                            v_val_2409_ = leanh::lean_ctor_get(v___x_2408_, 0);
                            leanh::lean_inc(v_val_2409_);
                            leanh::lean_dec_ref_known(v___x_2408_, 1);
                            v___x_2410_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2411_ = l_Lean_Syntax_getArg(v_stx_2395_, v___x_2410_);
                            v_fieldsAndSeps_2412_ = l_Lean_Syntax_getArgs(v___x_2411_);
                            leanh::lean_dec(v___x_2411_);
                            v___x_2428_ = l_Lean_Syntax_getTrailingTailPos_x3f(
                                v_stx_2395_,
                                v_isCursorOnWhitespace_2389_,
                            );
                            if leanh::lean_obj_tag(v___x_2428_) == 0 {
                                v___x_2429_ = l_Lean_Syntax_getTrailingTailPos_x3f(
                                    v_val_2404_,
                                    v_isCursorOnWhitespace_2389_,
                                );
                                v___y_2422_ = v___x_2429_;
                                state = 3;
                                continue;
                            } else {
                                v___y_2422_ = v___x_2428_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2408_);
                            leanh::lean_dec(v_stx_2395_);
                            leanh::lean_dec_ref(v_fileMap_2391_);
                            return v___x_2388_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_stx_2395_);
                    leanh::lean_dec_ref(v_fileMap_2391_);
                    return v___x_2388_;
                }
            }
            1 => {
                if v_isCursorInProperWhitespace_2390_ == 0 {
                    leanh::lean_dec(v_stx_2395_);
                    leanh::lean_dec_ref(v_fileMap_2391_);
                    return v___y_2397_;
                } else {
                    v___x_2398_ = l_Lean_Syntax_getPos_x3f(v_stx_2395_, v___y_2397_);
                    leanh::lean_dec(v_stx_2395_);
                    if leanh::lean_obj_tag(v___x_2398_) == 1 {
                        v_val_2399_ = leanh::lean_ctor_get(v___x_2398_, 0);
                        leanh::lean_inc(v_val_2399_);
                        leanh::lean_dec_ref_known(v___x_2398_, 1);
                        v___x_2400_ = l_Lean_FileMap_toPosition(v_fileMap_2391_, v_val_2399_);
                        leanh::lean_dec(v_val_2399_);
                        v_column_2401_ = leanh::lean_ctor_get(v___x_2400_, 1);
                        leanh::lean_inc(v_column_2401_);
                        leanh::lean_dec_ref(v___x_2400_);
                        v_column_2402_ = leanh::lean_ctor_get(v_hoverFilePos_2392_, 1);
                        v_isCursorInBlock_2403_ = lean_nat_dec_eq(v_column_2402_, v_column_2401_);
                        leanh::lean_dec(v_column_2401_);
                        return v_isCursorInBlock_2403_;
                    } else {
                        leanh::lean_dec(v___x_2398_);
                        leanh::lean_dec_ref(v_fileMap_2391_);
                        return v___y_2397_;
                    }
                }
            }
            2 => {
                if v___y_2414_ == 0 {
                    v___x_2415_ = l_Array_zipIdx___redArg(v_fieldsAndSeps_2412_, v___x_2410_);
                    leanh::lean_dec_ref(v_fieldsAndSeps_2412_);
                    v___x_2416_ = lean_array_get_size(v___x_2415_);
                    v___x_2417_ = lean_nat_dec_lt(v___x_2410_, v___x_2416_);
                    if v___x_2417_ == 0 {
                        leanh::lean_dec_ref(v___x_2415_);
                        v___y_2397_ = v___y_2414_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_2417_ == 0 {
                            leanh::lean_dec_ref(v___x_2415_);
                            v___y_2397_ = v___y_2414_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2418_ = 0usize;
                            v___x_2419_ = lean_usize_of_nat(v___x_2416_);
                            v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion_spec__0(v___y_2414_, v_hoverPos_2393_, v___x_2415_, v___x_2418_, v___x_2419_);
                            leanh::lean_dec_ref(v___x_2415_);
                            if v___x_2420_ == 0 {
                                v___y_2397_ = v___x_2420_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_stx_2395_);
                                leanh::lean_dec_ref(v_fileMap_2391_);
                                return v_isCursorOnWhitespace_2389_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fieldsAndSeps_2412_);
                    leanh::lean_dec(v_stx_2395_);
                    leanh::lean_dec_ref(v_fileMap_2391_);
                    return v_isCursorOnWhitespace_2389_;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_2422_) == 1 {
                    v_val_2423_ = leanh::lean_ctor_get(v___y_2422_, 0);
                    leanh::lean_inc(v_val_2423_);
                    leanh::lean_dec_ref_known(v___y_2422_, 1);
                    v___x_2424_ = lean_array_get_size(v_fieldsAndSeps_2412_);
                    v___x_2425_ = lean_nat_dec_eq(v___x_2424_, v___x_2410_);
                    if v___x_2425_ == 0 {
                        leanh::lean_dec(v_val_2423_);
                        leanh::lean_dec(v_val_2409_);
                        v___y_2414_ = v___x_2425_;
                        state = 2;
                        continue;
                    } else {
                        v_outerBounds_2426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_outerBounds_2426_, 0, v_val_2409_);
                        leanh::lean_ctor_set(v_outerBounds_2426_, 1, v_val_2423_);
                        v___x_2427_ = l_Lean_Syntax_Range_contains(
                            v_outerBounds_2426_,
                            v_hoverPos_2393_,
                            v_isCursorOnWhitespace_2389_,
                        );
                        leanh::lean_dec_ref_known(v_outerBounds_2426_, 2);
                        v___y_2414_ = v___x_2427_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2422_);
                    leanh::lean_dec_ref(v_fieldsAndSeps_2412_);
                    leanh::lean_dec(v_val_2409_);
                    leanh::lean_dec(v_stx_2395_);
                    leanh::lean_dec_ref(v_fileMap_2391_);
                    return v___x_2388_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed(
    mut v___x_2430_: *mut leanh::LeanObject,
    mut v_isCursorOnWhitespace_2431_: *mut leanh::LeanObject,
    mut v_isCursorInProperWhitespace_2432_: *mut leanh::LeanObject,
    mut v_fileMap_2433_: *mut leanh::LeanObject,
    mut v_hoverFilePos_2434_: *mut leanh::LeanObject,
    mut v_hoverPos_2435_: *mut leanh::LeanObject,
    mut v_leadingToken_x3f_2436_: *mut leanh::LeanObject,
    mut v_stx_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2473__boxed_2438_: u8 = 0;
    let mut v_isCursorOnWhitespace_boxed_2439_: u8 = 0;
    let mut v_isCursorInProperWhitespace_boxed_2440_: u8 = 0;
    let mut v_res_2441_: u8 = 0;
    let mut v_r_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2473__boxed_2438_ = (leanh::lean_unbox(v___x_2430_) as u8);
    v_isCursorOnWhitespace_boxed_2439_ =
        (leanh::lean_unbox(v_isCursorOnWhitespace_2431_) as u8);
    v_isCursorInProperWhitespace_boxed_2440_ =
        (leanh::lean_unbox(v_isCursorInProperWhitespace_2432_) as u8);
    v_res_2441_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0(v___x_2473__boxed_2438_, v_isCursorOnWhitespace_boxed_2439_, v_isCursorInProperWhitespace_boxed_2440_, v_fileMap_2433_, v_hoverFilePos_2434_, v_hoverPos_2435_, v_leadingToken_x3f_2436_, v_stx_2437_);
    leanh::lean_dec(v_leadingToken_x3f_2436_);
    leanh::lean_dec(v_hoverPos_2435_);
    leanh::lean_dec_ref(v_hoverFilePos_2434_);
    v_r_2442_ = leanh::lean_box((v_res_2441_) as usize);
    return v_r_2442_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(
    mut v_fileMap_2443_: *mut leanh::LeanObject,
    mut v_hoverPos_2444_: *mut leanh::LeanObject,
    mut v_cmdStx_2445_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_isCursorOnWhitespace_2446_: u8 = 0;
    v_isCursorOnWhitespace_2446_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorOnWhitespace(v_fileMap_2443_, v_hoverPos_2444_);
    if v_isCursorOnWhitespace_2446_ == 0 {
        leanh::lean_dec(v_cmdStx_2445_);
        leanh::lean_dec(v_hoverPos_2444_);
        leanh::lean_dec_ref(v_fileMap_2443_);
        return v_isCursorOnWhitespace_2446_;
    } else {
        let mut v_isCursorInProperWhitespace_2447_: u8 = 0;
        let mut v___x_2448_: u8 = 0;
        let mut v_hoverFilePos_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_isCursorInProperWhitespace_2447_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isCursorInProperWhitespace(v_fileMap_2443_, v_hoverPos_2444_);
        v___x_2448_ = 0;
        leanh::lean_inc_ref(v_fileMap_2443_);
        v_hoverFilePos_2449_ = l_Lean_FileMap_toPosition(v_fileMap_2443_, v_hoverPos_2444_);
        v___x_2450_ = leanh::lean_box((v___x_2448_) as usize);
        v___x_2451_ = leanh::lean_box((v_isCursorOnWhitespace_2446_) as usize);
        v___x_2452_ = leanh::lean_box((v_isCursorInProperWhitespace_2447_) as usize);
        v___f_2453_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___lam__0___boxed as *mut core::ffi::c_void, 8, 6);
        leanh::lean_closure_set(v___f_2453_, 0, v___x_2450_);
        leanh::lean_closure_set(v___f_2453_, 1, v___x_2451_);
        leanh::lean_closure_set(v___f_2453_, 2, v___x_2452_);
        leanh::lean_closure_set(v___f_2453_, 3, v_fileMap_2443_);
        leanh::lean_closure_set(v___f_2453_, 4, v_hoverFilePos_2449_);
        leanh::lean_closure_set(v___f_2453_, 5, v_hoverPos_2444_);
        v___x_2454_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findWithLeadingToken_x3f(v___f_2453_, v_cmdStx_2445_);
        if leanh::lean_obj_tag(v___x_2454_) == 0 {
            return v___x_2448_;
        } else {
            leanh::lean_dec_ref_known(v___x_2454_, 1);
            return v_isCursorOnWhitespace_2446_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion___boxed(
    mut v_fileMap_2455_: *mut leanh::LeanObject,
    mut v_hoverPos_2456_: *mut leanh::LeanObject,
    mut v_cmdStx_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2458_: u8 = 0;
    let mut v_r_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_2455_, v_hoverPos_2456_, v_cmdStx_2457_);
    v_r_2459_ = leanh::lean_box((v_res_2458_) as usize);
    return v_r_2459_;
}
pub unsafe fn l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(
    mut v_fileMap_2460_: *mut leanh::LeanObject,
    mut v_hoverPos_2461_: *mut leanh::LeanObject,
    mut v_cmdStx_2462_: *mut leanh::LeanObject,
    mut v_infoTree_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2464_: u8 = 0;
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v_fst_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCommandContextInfo_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_hoverPos_2461_);
                v___x_2464_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_isSyntheticStructFieldCompletion(v_fileMap_2460_, v_hoverPos_2461_, v_cmdStx_2462_);
                if v___x_2464_ == 0 {
                    leanh::lean_dec_ref(v_infoTree_2463_);
                    leanh::lean_dec(v_hoverPos_2461_);
                    v___x_2465_ = leanh::lean_box(0);
                    return v___x_2465_;
                } else {
                    v___x_2466_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findExpectedTypeAt(v_infoTree_2463_, v_hoverPos_2461_);
                    if leanh::lean_obj_tag(v___x_2466_) == 0 {
                        v___x_2467_ = leanh::lean_box(0);
                        return v___x_2467_;
                    } else {
                        v_val_2468_ = leanh::lean_ctor_get(v___x_2466_, 0);
                        v_isSharedCheck_2490_ =
                            (!leanh::lean_is_exclusive(v___x_2466_)) as u8;
                        if v_isSharedCheck_2490_ == 0 {
                            v___x_2470_ = v___x_2466_;
                            v_isShared_2471_ = v_isSharedCheck_2490_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2468_);
                            leanh::lean_dec(v___x_2466_);
                            v___x_2470_ = leanh::lean_box(0);
                            v_isShared_2471_ = v_isSharedCheck_2490_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2472_ = leanh::lean_ctor_get(v_val_2468_, 0);
                leanh::lean_inc(v_fst_2472_);
                v_snd_2473_ = leanh::lean_ctor_get(v_val_2468_, 1);
                leanh::lean_inc(v_snd_2473_);
                leanh::lean_dec(v_val_2468_);
                v___x_2474_ = l_Lean_Expr_getAppFn(v_snd_2473_);
                leanh::lean_dec(v_snd_2473_);
                if leanh::lean_obj_tag(v___x_2474_) == 4 {
                    v_toCommandContextInfo_2475_ = leanh::lean_ctor_get(v_fst_2472_, 0);
                    v_declName_2476_ = leanh::lean_ctor_get(v___x_2474_, 0);
                    leanh::lean_inc_n(v_declName_2476_, 2);
                    leanh::lean_dec_ref_known(v___x_2474_, 2);
                    v_env_2477_ = leanh::lean_ctor_get(v_toCommandContextInfo_2475_, 0);
                    leanh::lean_inc_ref(v_env_2477_);
                    v___x_2478_ = l_Lean_isStructure(v_env_2477_, v_declName_2476_);
                    if v___x_2478_ == 0 {
                        leanh::lean_dec(v_declName_2476_);
                        leanh::lean_dec(v_fst_2472_);
                        leanh::lean_del_object(v___x_2470_);
                        v___x_2479_ = leanh::lean_box(0);
                        return v___x_2479_;
                    } else {
                        v___x_2480_ = leanh::lean_box(0);
                        v___x_2481_ = leanh::lean_box(0);
                        v___x_2482_ = leanh::lean_box(0);
                        v___x_2483_ = l_Lean_LocalContext_empty;
                        v___x_2484_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_2484_, 0, v___x_2481_);
                        leanh::lean_ctor_set(v___x_2484_, 1, v___x_2482_);
                        leanh::lean_ctor_set(v___x_2484_, 2, v___x_2483_);
                        leanh::lean_ctor_set(v___x_2484_, 3, v_declName_2476_);
                        v___x_2485_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2485_, 0, v___x_2480_);
                        leanh::lean_ctor_set(v___x_2485_, 1, v_fst_2472_);
                        leanh::lean_ctor_set(v___x_2485_, 2, v___x_2484_);
                        if v_isShared_2471_ == 0 {
                            leanh::lean_ctor_set(v___x_2470_, 0, v___x_2485_);
                            v___x_2487_ = v___x_2470_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2488_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
                            v___x_2487_ = v_reuseFailAlloc_2488_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2474_);
                    leanh::lean_dec(v_fst_2472_);
                    leanh::lean_del_object(v___x_2470_);
                    v___x_2489_ = leanh::lean_box(0);
                    return v___x_2489_;
                }
            }
            2 => {
                return v___x_2487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_findSyntheticCompletions(
    mut v_fileMap_2493_: *mut leanh::LeanObject,
    mut v_hoverPos_2494_: *mut leanh::LeanObject,
    mut v_cmdStx_2495_: *mut leanh::LeanObject,
    mut v_infoTree_2496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_infoTree_2496_);
                leanh::lean_inc(v_cmdStx_2495_);
                leanh::lean_inc_ref(v_fileMap_2493_);
                v___x_2504_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticTacticCompletion_x3f(v_fileMap_2493_, v_hoverPos_2494_, v_cmdStx_2495_, v_infoTree_2496_);
                if leanh::lean_obj_tag(v___x_2504_) == 0 {
                    leanh::lean_inc_ref(v_infoTree_2496_);
                    leanh::lean_inc(v_hoverPos_2494_);
                    v___x_2505_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticFieldCompletion_x3f(v_fileMap_2493_, v_hoverPos_2494_, v_cmdStx_2495_, v_infoTree_2496_);
                    if leanh::lean_obj_tag(v___x_2505_) == 0 {
                        v___x_2506_ = l___private_Lean_Server_Completion_SyntheticCompletion_0__Lean_Server_Completion_findSyntheticIdentifierCompletion_x3f(v_hoverPos_2494_, v_infoTree_2496_);
                        v___y_2498_ = v___x_2506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_infoTree_2496_);
                        leanh::lean_dec(v_hoverPos_2494_);
                        v___y_2498_ = v___x_2505_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_infoTree_2496_);
                    leanh::lean_dec(v_cmdStx_2495_);
                    leanh::lean_dec(v_hoverPos_2494_);
                    leanh::lean_dec_ref(v_fileMap_2493_);
                    v___y_2498_ = v___x_2504_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2498_) == 0 {
                    v___x_2499_ = l_Lean_Server_Completion_findSyntheticCompletions___closed__0;
                    return v___x_2499_;
                } else {
                    v_val_2500_ = leanh::lean_ctor_get(v___y_2498_, 0);
                    leanh::lean_inc(v_val_2500_);
                    leanh::lean_dec_ref_known(v___y_2498_, 1);
                    v___x_2501_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2501_);
                    v___x_2503_ = lean_array_push(v___x_2502_, v_val_2500_);
                    return v___x_2503_;
                }
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_SyntheticCompletion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_SyntheticCompletion(
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
pub unsafe fn initialize_Lean_Server_Completion_SyntheticCompletion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
}