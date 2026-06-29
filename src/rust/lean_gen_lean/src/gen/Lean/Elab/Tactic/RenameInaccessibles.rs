// Lean compiler output
// Module: Lean.Elab.Tactic.RenameInaccessibles
// Imports: Lean.Elab.Term Lean.Elab.Binders
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_extractMacroScopes, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_append___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Data::Position::{
    l_Lean_FileMap_toPosition, l_Lean_instInhabitedFileMap_default,
};
use crate::r#gen::Lean::Elab::Binders::{
    initialize_Lean_Elab_Binders, l_Lean_Elab_Term_addLocalVarInfo,
    runtime_initialize_Lean_Elab_Binders,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoTree_substitute;
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_MacroScopesView_equalScope;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_getAt_x3f, l_Lean_LocalContext_setUserName, l_Lean_LocalDecl_fvarId,
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_userName, lean_local_ctx_num_indices,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
    l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,13771926289831477797 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        116, 111, 111, 32, 109, 97, 110, 121, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110, 97,
        109, 101, 115, 32, 112, 114, 111, 118, 105, 100, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value:
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
pub static mut l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(
    mut v_x_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1719_);
    crate::leanh::lean_inc_ref(v___y_1718_);
    v___x_1725_ = crate::leanh::lean_apply_7(
        v_x_1717_,
        v___y_1718_,
        v___y_1719_,
        v___y_1720_,
        v___y_1721_,
        v___y_1722_,
        v___y_1723_,
        crate::leanh::lean_box(0),
    );
    return v___x_1725_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed(
    mut v_x_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
    crate::leanh::lean_dec(v___y_1728_);
    crate::leanh::lean_dec_ref(v___y_1727_);
    return v_res_1734_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(
    mut v_mvarId_1735_: *mut crate::leanh::LeanObject,
    mut v_x_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1749_: u8 = 0;
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1738_);
                crate::leanh::lean_inc_ref(v___y_1737_);
                v___f_1744_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_1744_, 0, v_x_1736_);
                crate::leanh::lean_closure_set(v___f_1744_, 1, v___y_1737_);
                crate::leanh::lean_closure_set(v___f_1744_, 2, v___y_1738_);
                v___x_1745_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1735_,
                    v___f_1744_,
                    v___y_1739_,
                    v___y_1740_,
                    v___y_1741_,
                    v___y_1742_,
                );
                if crate::leanh::lean_obj_tag(v___x_1745_) == 0 {
                    return v___x_1745_;
                } else {
                    v_a_1746_ = crate::leanh::lean_ctor_get(v___x_1745_, 0);
                    v_isSharedCheck_1753_ = (!crate::leanh::lean_is_exclusive(v___x_1745_)) as u8;
                    if v_isSharedCheck_1753_ == 0 {
                        v___x_1748_ = v___x_1745_;
                        v_isShared_1749_ = v_isSharedCheck_1753_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1746_);
                        crate::leanh::lean_dec(v___x_1745_);
                        v___x_1748_ = crate::leanh::lean_box(0);
                        v_isShared_1749_ = v_isSharedCheck_1753_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1749_ == 0 {
                    v___x_1751_ = v___x_1748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
                    v___x_1751_ = v_reuseFailAlloc_1752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___boxed(
    mut v_mvarId_1754_: *mut crate::leanh::LeanObject,
    mut v_x_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(
            v_mvarId_1754_,
            v_x_1755_,
            v___y_1756_,
            v___y_1757_,
            v___y_1758_,
            v___y_1759_,
            v___y_1760_,
            v___y_1761_,
        );
    crate::leanh::lean_dec(v___y_1761_);
    crate::leanh::lean_dec_ref(v___y_1760_);
    crate::leanh::lean_dec(v___y_1759_);
    crate::leanh::lean_dec_ref(v___y_1758_);
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(
    mut v_00_u03b1_1764_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1765_: *mut crate::leanh::LeanObject,
    mut v_x_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
    mut v___y_1769_: *mut crate::leanh::LeanObject,
    mut v___y_1770_: *mut crate::leanh::LeanObject,
    mut v___y_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(
            v_mvarId_1765_,
            v_x_1766_,
            v___y_1767_,
            v___y_1768_,
            v___y_1769_,
            v___y_1770_,
            v___y_1771_,
            v___y_1772_,
        );
    return v___x_1774_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1776_: *mut crate::leanh::LeanObject,
    mut v_x_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(
        v_00_u03b1_1775_,
        v_mvarId_1776_,
        v_x_1777_,
        v___y_1778_,
        v___y_1779_,
        v___y_1780_,
        v___y_1781_,
        v___y_1782_,
        v___y_1783_,
    );
    crate::leanh::lean_dec(v___y_1783_);
    crate::leanh::lean_dec_ref(v___y_1782_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    crate::leanh::lean_dec(v___y_1779_);
    crate::leanh::lean_dec_ref(v___y_1778_);
    return v_res_1785_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(
    mut v_as_1786_: *mut crate::leanh::LeanObject,
    mut v_sz_1787_: usize,
    mut v_i_1788_: usize,
    mut v_b_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: usize = 0;
    let mut v___x_1806_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1797_ = lean_usize_dec_lt(v_i_1788_, v_sz_1787_);
                if v___x_1797_ == 0 {
                    v___x_1798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1798_, 0, v_b_1789_);
                    return v___x_1798_;
                } else {
                    v_a_1799_ = lean_array_uget_borrowed(v_as_1786_, v_i_1788_);
                    v_fst_1800_ = crate::leanh::lean_ctor_get(v_a_1799_, 0);
                    v_snd_1801_ = crate::leanh::lean_ctor_get(v_a_1799_, 1);
                    crate::leanh::lean_inc(v_fst_1800_);
                    v___x_1802_ = l_Lean_mkFVar(v_fst_1800_);
                    crate::leanh::lean_inc(v_snd_1801_);
                    v___x_1803_ = l_Lean_Elab_Term_addLocalVarInfo(
                        v_snd_1801_,
                        v___x_1802_,
                        v___y_1790_,
                        v___y_1791_,
                        v___y_1792_,
                        v___y_1793_,
                        v___y_1794_,
                        v___y_1795_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1803_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1803_, 1);
                        v___x_1804_ = crate::leanh::lean_box(0);
                        v___x_1805_ = 1usize;
                        v___x_1806_ = lean_usize_add(v_i_1788_, v___x_1805_);
                        v_i_1788_ = v___x_1806_;
                        v_b_1789_ = v___x_1804_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1803_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0___boxed(
    mut v_as_1808_: *mut crate::leanh::LeanObject,
    mut v_sz_1809_: *mut crate::leanh::LeanObject,
    mut v_i_1810_: *mut crate::leanh::LeanObject,
    mut v_b_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1819_: usize = 0;
    let mut v_i_boxed_1820_: usize = 0;
    let mut v_res_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1819_ = crate::leanh::lean_unbox_usize(v_sz_1809_);
    crate::leanh::lean_dec(v_sz_1809_);
    v_i_boxed_1820_ = crate::leanh::lean_unbox_usize(v_i_1810_);
    crate::leanh::lean_dec(v_i_1810_);
    v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_as_1808_, v_sz_boxed_1819_, v_i_boxed_1820_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
    crate::leanh::lean_dec(v___y_1817_);
    crate::leanh::lean_dec_ref(v___y_1816_);
    crate::leanh::lean_dec(v___y_1815_);
    crate::leanh::lean_dec_ref(v___y_1814_);
    crate::leanh::lean_dec(v___y_1813_);
    crate::leanh::lean_dec_ref(v___y_1812_);
    crate::leanh::lean_dec_ref(v_as_1808_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles___lam__0(
    mut v_fst_1822_: *mut crate::leanh::LeanObject,
    mut v_sz_1823_: usize,
    mut v___x_1824_: usize,
    mut v___x_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_fst_1822_, v_sz_1823_, v___x_1824_, v___x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
                if crate::leanh::lean_obj_tag(v___x_1833_) == 0 {
                    v_isSharedCheck_1840_ = (!crate::leanh::lean_is_exclusive(v___x_1833_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v_unused_1841_ = crate::leanh::lean_ctor_get(v___x_1833_, 0);
                        crate::leanh::lean_dec(v_unused_1841_);
                        v___x_1835_ = v___x_1833_;
                        v_isShared_1836_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1833_);
                        v___x_1835_ = crate::leanh::lean_box(0);
                        v_isShared_1836_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1833_;
                }
            }
            1 => {
                if v_isShared_1836_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1835_, 0, v___x_1825_);
                    v___x_1838_ = v___x_1835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1825_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed(
    mut v_fst_1842_: *mut crate::leanh::LeanObject,
    mut v_sz_1843_: *mut crate::leanh::LeanObject,
    mut v___x_1844_: *mut crate::leanh::LeanObject,
    mut v___x_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1853_: usize = 0;
    let mut v___x_22490__boxed_1854_: usize = 0;
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1853_ = crate::leanh::lean_unbox_usize(v_sz_1843_);
    crate::leanh::lean_dec(v_sz_1843_);
    v___x_22490__boxed_1854_ = crate::leanh::lean_unbox_usize(v___x_1844_);
    crate::leanh::lean_dec(v___x_1844_);
    v_res_1855_ = l_Lean_Elab_Tactic_renameInaccessibles___lam__0(
        v_fst_1842_,
        v_sz_boxed_1853_,
        v___x_22490__boxed_1854_,
        v___x_1845_,
        v___y_1846_,
        v___y_1847_,
        v___y_1848_,
        v___y_1849_,
        v___y_1850_,
        v___y_1851_,
    );
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    crate::leanh::lean_dec(v___y_1847_);
    crate::leanh::lean_dec_ref(v___y_1846_);
    crate::leanh::lean_dec(v_fst_1842_);
    return v_res_1855_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1857_ = lean_mk_empty_array_with_capacity(v___x_1856_);
    v___x_1858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: usize = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = 5usize;
    v___x_1860_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1861_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1862_ = lean_mk_empty_array_with_capacity(v___x_1861_);
    v___x_1863_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0);
    v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1863_);
    crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1860_);
    crate::leanh::lean_ctor_set(v___x_1864_, 3, v___x_1860_);
    crate::leanh::lean_ctor_set_usize(v___x_1864_, 4, v___x_1859_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v_enabled_1883_: u8 = 0;
    let mut v_assignment_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v_unused_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1867_ = lean_st_ref_get(v___y_1865_);
                v_infoState_1868_ = crate::leanh::lean_ctor_get(v___x_1867_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1868_);
                crate::leanh::lean_dec(v___x_1867_);
                v_trees_1869_ = crate::leanh::lean_ctor_get(v_infoState_1868_, 2);
                crate::leanh::lean_inc_ref(v_trees_1869_);
                crate::leanh::lean_dec_ref(v_infoState_1868_);
                v___x_1870_ = lean_st_ref_take(v___y_1865_);
                v_infoState_1871_ = crate::leanh::lean_ctor_get(v___x_1870_, 7);
                v_env_1872_ = crate::leanh::lean_ctor_get(v___x_1870_, 0);
                v_nextMacroScope_1873_ = crate::leanh::lean_ctor_get(v___x_1870_, 1);
                v_ngen_1874_ = crate::leanh::lean_ctor_get(v___x_1870_, 2);
                v_auxDeclNGen_1875_ = crate::leanh::lean_ctor_get(v___x_1870_, 3);
                v_traceState_1876_ = crate::leanh::lean_ctor_get(v___x_1870_, 4);
                v_cache_1877_ = crate::leanh::lean_ctor_get(v___x_1870_, 5);
                v_messages_1878_ = crate::leanh::lean_ctor_get(v___x_1870_, 6);
                v_snapshotTasks_1879_ = crate::leanh::lean_ctor_get(v___x_1870_, 8);
                v_isSharedCheck_1900_ = (!crate::leanh::lean_is_exclusive(v___x_1870_)) as u8;
                if v_isSharedCheck_1900_ == 0 {
                    v___x_1881_ = v___x_1870_;
                    v_isShared_1882_ = v_isSharedCheck_1900_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1879_);
                    crate::leanh::lean_inc(v_infoState_1871_);
                    crate::leanh::lean_inc(v_messages_1878_);
                    crate::leanh::lean_inc(v_cache_1877_);
                    crate::leanh::lean_inc(v_traceState_1876_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1875_);
                    crate::leanh::lean_inc(v_ngen_1874_);
                    crate::leanh::lean_inc(v_nextMacroScope_1873_);
                    crate::leanh::lean_inc(v_env_1872_);
                    crate::leanh::lean_dec(v___x_1870_);
                    v___x_1881_ = crate::leanh::lean_box(0);
                    v_isShared_1882_ = v_isSharedCheck_1900_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1883_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1884_ = crate::leanh::lean_ctor_get(v_infoState_1871_, 0);
                v_lazyAssignment_1885_ = crate::leanh::lean_ctor_get(v_infoState_1871_, 1);
                v_isSharedCheck_1898_ = (!crate::leanh::lean_is_exclusive(v_infoState_1871_)) as u8;
                if v_isSharedCheck_1898_ == 0 {
                    v_unused_1899_ = crate::leanh::lean_ctor_get(v_infoState_1871_, 2);
                    crate::leanh::lean_dec(v_unused_1899_);
                    v___x_1887_ = v_infoState_1871_;
                    v_isShared_1888_ = v_isSharedCheck_1898_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1885_);
                    crate::leanh::lean_inc(v_assignment_1884_);
                    crate::leanh::lean_dec(v_infoState_1871_);
                    v___x_1887_ = crate::leanh::lean_box(0);
                    v_isShared_1888_ = v_isSharedCheck_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1);
                if v_isShared_1888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1887_, 2, v___x_1889_);
                    v___x_1891_ = v___x_1887_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_assignment_1884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_lazyAssignment_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___x_1889_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1897_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1883_,
                    );
                    v___x_1891_ = v_reuseFailAlloc_1897_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1881_, 7, v___x_1891_);
                    v___x_1893_ = v___x_1881_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_env_1872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_nextMacroScope_1873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_ngen_1874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_auxDeclNGen_1875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_traceState_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_cache_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_messages_1878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 7, v___x_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_snapshotTasks_1879_);
                    v___x_1893_ = v_reuseFailAlloc_1896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1894_ = lean_st_ref_set(v___y_1865_, v___x_1893_);
                v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1895_, 0, v_trees_1869_);
                return v___x_1895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___boxed(
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1901_);
    crate::leanh::lean_dec(v___y_1901_);
    return v_res_1903_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(
    mut v___x_1904_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1905_: *mut crate::leanh::LeanObject,
    mut v_sz_1906_: usize,
    mut v_i_1907_: usize,
    mut v_bs_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1916_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
                if v___x_1916_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_1905_);
                    v___x_1917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1917_, 0, v_bs_1908_);
                    return v___x_1917_;
                } else {
                    v_assignment_1918_ = crate::leanh::lean_ctor_get(v___x_1904_, 0);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_1905_);
                    crate::leanh::lean_inc(v___y_1914_);
                    crate::leanh::lean_inc_ref(v___y_1913_);
                    crate::leanh::lean_inc(v___y_1912_);
                    crate::leanh::lean_inc_ref(v___y_1911_);
                    crate::leanh::lean_inc(v___y_1910_);
                    crate::leanh::lean_inc_ref(v___y_1909_);
                    v___x_1919_ = crate::leanh::lean_apply_7(
                        v_ctx_x3f_1905_,
                        v___y_1909_,
                        v___y_1910_,
                        v___y_1911_,
                        v___y_1912_,
                        v___y_1913_,
                        v___y_1914_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1919_) == 0 {
                        v_a_1920_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                        crate::leanh::lean_inc(v_a_1920_);
                        crate::leanh::lean_dec_ref_known(v___x_1919_, 1);
                        v_v_1921_ = lean_array_uget(v_bs_1908_, v_i_1907_);
                        v___x_1922_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1923_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1922_);
                        v_tree_1930_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_1921_, v_assignment_1918_);
                        if crate::leanh::lean_obj_tag(v_a_1920_) == 0 {
                            v_a_1925_ = v_tree_1930_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1931_ = crate::leanh::lean_ctor_get(v_a_1920_, 0);
                            crate::leanh::lean_inc(v_val_1931_);
                            crate::leanh::lean_dec_ref_known(v_a_1920_, 1);
                            v___x_1932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1932_, 0, v_val_1931_);
                            crate::leanh::lean_ctor_set(v___x_1932_, 1, v_tree_1930_);
                            v_a_1925_ = v___x_1932_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1908_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_1905_);
                        v_a_1933_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                        v_isSharedCheck_1940_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1919_)) as u8;
                        if v_isSharedCheck_1940_ == 0 {
                            v___x_1935_ = v___x_1919_;
                            v_isShared_1936_ = v_isSharedCheck_1940_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1933_);
                            crate::leanh::lean_dec(v___x_1919_);
                            v___x_1935_ = crate::leanh::lean_box(0);
                            v_isShared_1936_ = v_isSharedCheck_1940_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1926_ = 1usize;
                v___x_1927_ = lean_usize_add(v_i_1907_, v___x_1926_);
                v___x_1928_ = lean_array_uset(v_bs_x27_1923_, v_i_1907_, v_a_1925_);
                v_i_1907_ = v___x_1927_;
                v_bs_1908_ = v___x_1928_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1936_ == 0 {
                    v___x_1938_ = v___x_1935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12___boxed(
    mut v___x_1941_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1942_: *mut crate::leanh::LeanObject,
    mut v_sz_1943_: *mut crate::leanh::LeanObject,
    mut v_i_1944_: *mut crate::leanh::LeanObject,
    mut v_bs_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1953_: usize = 0;
    let mut v_i_boxed_1954_: usize = 0;
    let mut v_res_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1953_ = crate::leanh::lean_unbox_usize(v_sz_1943_);
    crate::leanh::lean_dec(v_sz_1943_);
    v_i_boxed_1954_ = crate::leanh::lean_unbox_usize(v_i_1944_);
    crate::leanh::lean_dec(v_i_1944_);
    v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_1941_, v_ctx_x3f_1942_, v_sz_boxed_1953_, v_i_boxed_1954_, v_bs_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
    crate::leanh::lean_dec(v___y_1951_);
    crate::leanh::lean_dec_ref(v___y_1950_);
    crate::leanh::lean_dec(v___y_1949_);
    crate::leanh::lean_dec_ref(v___y_1948_);
    crate::leanh::lean_dec(v___y_1947_);
    crate::leanh::lean_dec_ref(v___y_1946_);
    crate::leanh::lean_dec_ref(v___x_1941_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(
    mut v___x_1956_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_sz_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_isSharedCheck_1992_: u8 = 0;
    let mut v_vs_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v_sz_1997_: usize = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1958_) == 0 {
                    v_cs_1966_ = crate::leanh::lean_ctor_get(v_x_1958_, 0);
                    v_isSharedCheck_1992_ = (!crate::leanh::lean_is_exclusive(v_x_1958_)) as u8;
                    if v_isSharedCheck_1992_ == 0 {
                        v___x_1968_ = v_x_1958_;
                        v_isShared_1969_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_1966_);
                        crate::leanh::lean_dec(v_x_1958_);
                        v___x_1968_ = crate::leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1993_ = crate::leanh::lean_ctor_get(v_x_1958_, 0);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v_x_1958_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1995_ = v_x_1958_;
                        v_isShared_1996_ = v_isSharedCheck_2019_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1993_);
                        crate::leanh::lean_dec(v_x_1958_);
                        v___x_1995_ = crate::leanh::lean_box(0);
                        v_isShared_1996_ = v_isSharedCheck_2019_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1970_ = lean_array_size(v_cs_1966_);
                v___x_1971_ = 0usize;
                v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_1956_, v_ctx_x3f_1957_, v_sz_1970_, v___x_1971_, v_cs_1966_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
                if crate::leanh::lean_obj_tag(v___x_1972_) == 0 {
                    v_a_1973_ = crate::leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_1983_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1973_);
                        crate::leanh::lean_dec(v___x_1972_);
                        v___x_1975_ = crate::leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1983_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1968_);
                    v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1986_ = v___x_1972_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1984_);
                        crate::leanh::lean_dec(v___x_1972_);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1968_, 0, v_a_1973_);
                    v___x_1978_ = v___x_1968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1975_, 0, v___x_1978_);
                    v___x_1980_ = v___x_1975_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1980_;
            }
            5 => {
                if v_isShared_1987_ == 0 {
                    v___x_1989_ = v___x_1986_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1989_;
            }
            7 => {
                v_sz_1997_ = lean_array_size(v_vs_1993_);
                v___x_1998_ = 0usize;
                v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_1956_, v_ctx_x3f_1957_, v_sz_1997_, v___x_1998_, v_vs_1993_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
                if crate::leanh::lean_obj_tag(v___x_1999_) == 0 {
                    v_a_2000_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2002_ = v___x_1999_;
                        v_isShared_2003_ = v_isSharedCheck_2010_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2000_);
                        crate::leanh::lean_dec(v___x_1999_);
                        v___x_2002_ = crate::leanh::lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2010_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1995_);
                    v_a_2011_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2018_ = (!crate::leanh::lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_1999_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2011_);
                        crate::leanh::lean_dec(v___x_1999_);
                        v___x_2013_ = crate::leanh::lean_box(0);
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v_a_2000_);
                    v___x_2005_ = v___x_1995_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2009_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2002_, 0, v___x_2005_);
                    v___x_2007_ = v___x_2002_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2007_;
            }
            11 => {
                if v_isShared_2014_ == 0 {
                    v___x_2016_ = v___x_2013_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
                    v___x_2016_ = v_reuseFailAlloc_2017_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(
    mut v___x_2020_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2021_: *mut crate::leanh::LeanObject,
    mut v_sz_2022_: usize,
    mut v_i_2023_: usize,
    mut v_bs_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2032_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
                if v___x_2032_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2021_);
                    v___x_2033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2033_, 0, v_bs_2024_);
                    return v___x_2033_;
                } else {
                    v_v_2034_ = lean_array_uget_borrowed(v_bs_2024_, v_i_2023_);
                    crate::leanh::lean_inc(v_v_2034_);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_2021_);
                    v___x_2035_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2020_, v_ctx_x3f_2021_, v_v_2034_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
                    if crate::leanh::lean_obj_tag(v___x_2035_) == 0 {
                        v_a_2036_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                        crate::leanh::lean_inc(v_a_2036_);
                        crate::leanh::lean_dec_ref_known(v___x_2035_, 1);
                        v___x_2037_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2038_ = lean_array_uset(v_bs_2024_, v_i_2023_, v___x_2037_);
                        v___x_2039_ = 1usize;
                        v___x_2040_ = lean_usize_add(v_i_2023_, v___x_2039_);
                        v___x_2041_ = lean_array_uset(v_bs_x27_2038_, v_i_2023_, v_a_2036_);
                        v_i_2023_ = v___x_2040_;
                        v_bs_2024_ = v___x_2041_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2024_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_2021_);
                        v_a_2043_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                        v_isSharedCheck_2050_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v___x_2045_ = v___x_2035_;
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2043_);
                            crate::leanh::lean_dec(v___x_2035_);
                            v___x_2045_ = crate::leanh::lean_box(0);
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2046_ == 0 {
                    v___x_2048_ = v___x_2045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
                    v___x_2048_ = v_reuseFailAlloc_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14___boxed(
    mut v___x_2051_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2052_: *mut crate::leanh::LeanObject,
    mut v_sz_2053_: *mut crate::leanh::LeanObject,
    mut v_i_2054_: *mut crate::leanh::LeanObject,
    mut v_bs_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2063_: usize = 0;
    let mut v_i_boxed_2064_: usize = 0;
    let mut v_res_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2063_ = crate::leanh::lean_unbox_usize(v_sz_2053_);
    crate::leanh::lean_dec(v_sz_2053_);
    v_i_boxed_2064_ = crate::leanh::lean_unbox_usize(v_i_2054_);
    crate::leanh::lean_dec(v_i_2054_);
    v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_2051_, v_ctx_x3f_2052_, v_sz_boxed_2063_, v_i_boxed_2064_, v_bs_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
    crate::leanh::lean_dec(v___y_2061_);
    crate::leanh::lean_dec_ref(v___y_2060_);
    crate::leanh::lean_dec(v___y_2059_);
    crate::leanh::lean_dec_ref(v___y_2058_);
    crate::leanh::lean_dec(v___y_2057_);
    crate::leanh::lean_dec_ref(v___y_2056_);
    crate::leanh::lean_dec_ref(v___x_2051_);
    return v_res_2065_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11___boxed(
    mut v___x_2066_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2067_: *mut crate::leanh::LeanObject,
    mut v_x_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
    mut v___y_2074_: *mut crate::leanh::LeanObject,
    mut v___y_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2066_, v_ctx_x3f_2067_, v_x_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
    crate::leanh::lean_dec(v___y_2074_);
    crate::leanh::lean_dec_ref(v___y_2073_);
    crate::leanh::lean_dec(v___y_2072_);
    crate::leanh::lean_dec_ref(v___y_2071_);
    crate::leanh::lean_dec(v___y_2070_);
    crate::leanh::lean_dec_ref(v___y_2069_);
    crate::leanh::lean_dec_ref(v___x_2066_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(
    mut v___x_2077_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2078_: *mut crate::leanh::LeanObject,
    mut v_t_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_2090_: usize = 0;
    let mut v_tailOff_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2097_: usize = 0;
    let mut v___x_2098_: usize = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2087_ = crate::leanh::lean_ctor_get(v_t_2079_, 0);
                v_tail_2088_ = crate::leanh::lean_ctor_get(v_t_2079_, 1);
                v_size_2089_ = crate::leanh::lean_ctor_get(v_t_2079_, 2);
                v_shift_2090_ = crate::leanh::lean_ctor_get_usize(v_t_2079_, 4);
                v_tailOff_2091_ = crate::leanh::lean_ctor_get(v_t_2079_, 3);
                v_isSharedCheck_2127_ = (!crate::leanh::lean_is_exclusive(v_t_2079_)) as u8;
                if v_isSharedCheck_2127_ == 0 {
                    v___x_2093_ = v_t_2079_;
                    v_isShared_2094_ = v_isSharedCheck_2127_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_2091_);
                    crate::leanh::lean_inc(v_size_2089_);
                    crate::leanh::lean_inc(v_tail_2088_);
                    crate::leanh::lean_inc(v_root_2087_);
                    crate::leanh::lean_dec(v_t_2079_);
                    v___x_2093_ = crate::leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_ctx_x3f_2078_);
                v___x_2095_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2077_, v_ctx_x3f_2078_, v_root_2087_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
                if crate::leanh::lean_obj_tag(v___x_2095_) == 0 {
                    v_a_2096_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                    crate::leanh::lean_inc(v_a_2096_);
                    crate::leanh::lean_dec_ref_known(v___x_2095_, 1);
                    v_sz_2097_ = lean_array_size(v_tail_2088_);
                    v___x_2098_ = 0usize;
                    v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_2077_, v_ctx_x3f_2078_, v_sz_2097_, v___x_2098_, v_tail_2088_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
                    if crate::leanh::lean_obj_tag(v___x_2099_) == 0 {
                        v_a_2100_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                        v_isSharedCheck_2110_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2099_)) as u8;
                        if v_isSharedCheck_2110_ == 0 {
                            v___x_2102_ = v___x_2099_;
                            v_isShared_2103_ = v_isSharedCheck_2110_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2100_);
                            crate::leanh::lean_dec(v___x_2099_);
                            v___x_2102_ = crate::leanh::lean_box(0);
                            v_isShared_2103_ = v_isSharedCheck_2110_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2096_);
                        crate::leanh::lean_del_object(v___x_2093_);
                        crate::leanh::lean_dec(v_tailOff_2091_);
                        crate::leanh::lean_dec(v_size_2089_);
                        v_a_2111_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                        v_isSharedCheck_2118_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2099_)) as u8;
                        if v_isSharedCheck_2118_ == 0 {
                            v___x_2113_ = v___x_2099_;
                            v_isShared_2114_ = v_isSharedCheck_2118_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2111_);
                            crate::leanh::lean_dec(v___x_2099_);
                            v___x_2113_ = crate::leanh::lean_box(0);
                            v_isShared_2114_ = v_isSharedCheck_2118_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2093_);
                    crate::leanh::lean_dec(v_tailOff_2091_);
                    crate::leanh::lean_dec(v_size_2089_);
                    crate::leanh::lean_dec_ref(v_tail_2088_);
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2078_);
                    v_a_2119_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2126_ = (!crate::leanh::lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2126_ == 0 {
                        v___x_2121_ = v___x_2095_;
                        v_isShared_2122_ = v_isSharedCheck_2126_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2119_);
                        crate::leanh::lean_dec(v___x_2095_);
                        v___x_2121_ = crate::leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2126_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2093_, 1, v_a_2100_);
                    crate::leanh::lean_ctor_set(v___x_2093_, 0, v_a_2096_);
                    v___x_2105_ = v___x_2093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_a_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_size_2089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_tailOff_2091_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_2109_, 4, v_shift_2090_);
                    v___x_2105_ = v_reuseFailAlloc_2109_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2105_);
                    v___x_2107_ = v___x_2102_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
                    v___x_2107_ = v_reuseFailAlloc_2108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2107_;
            }
            5 => {
                if v_isShared_2114_ == 0 {
                    v___x_2116_ = v___x_2113_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2116_;
            }
            7 => {
                if v_isShared_2122_ == 0 {
                    v___x_2124_ = v___x_2121_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
                    v___x_2124_ = v_reuseFailAlloc_2125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6___boxed(
    mut v___x_2128_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2129_: *mut crate::leanh::LeanObject,
    mut v_t_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v___x_2128_, v_ctx_x3f_2129_, v_t_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
    crate::leanh::lean_dec(v___y_2136_);
    crate::leanh::lean_dec_ref(v___y_2135_);
    crate::leanh::lean_dec(v___y_2134_);
    crate::leanh::lean_dec_ref(v___y_2133_);
    crate::leanh::lean_dec(v___y_2132_);
    crate::leanh::lean_dec_ref(v___y_2131_);
    crate::leanh::lean_dec_ref(v___x_2128_);
    return v_res_2138_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v_a_2146_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v_enabled_2170_: u8 = 0;
    let mut v_assignment_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_unused_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_a_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2149_ = lean_st_ref_get(v___y_2139_);
                v_infoState_2150_ = crate::leanh::lean_ctor_get(v___x_2149_, 7);
                crate::leanh::lean_inc_ref(v_infoState_2150_);
                crate::leanh::lean_dec(v___x_2149_);
                v_trees_2151_ = crate::leanh::lean_ctor_get(v_infoState_2150_, 2);
                crate::leanh::lean_inc_ref(v_trees_2151_);
                v___x_2152_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v_infoState_2150_, v_ctx_x3f_2140_, v_trees_2151_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2139_);
                crate::leanh::lean_dec_ref(v_infoState_2150_);
                if crate::leanh::lean_obj_tag(v___x_2152_) == 0 {
                    v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2191_ = (!crate::leanh::lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2155_ = v___x_2152_;
                        v_isShared_2156_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2153_);
                        crate::leanh::lean_dec(v___x_2152_);
                        v___x_2155_ = crate::leanh::lean_box(0);
                        v_isShared_2156_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2146_);
                    v_a_2192_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2199_ = (!crate::leanh::lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2199_ == 0 {
                        v___x_2194_ = v___x_2152_;
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2192_);
                        crate::leanh::lean_dec(v___x_2152_);
                        v___x_2194_ = crate::leanh::lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2157_ = lean_st_ref_take(v___y_2139_);
                v_infoState_2158_ = crate::leanh::lean_ctor_get(v___x_2157_, 7);
                v_env_2159_ = crate::leanh::lean_ctor_get(v___x_2157_, 0);
                v_nextMacroScope_2160_ = crate::leanh::lean_ctor_get(v___x_2157_, 1);
                v_ngen_2161_ = crate::leanh::lean_ctor_get(v___x_2157_, 2);
                v_auxDeclNGen_2162_ = crate::leanh::lean_ctor_get(v___x_2157_, 3);
                v_traceState_2163_ = crate::leanh::lean_ctor_get(v___x_2157_, 4);
                v_cache_2164_ = crate::leanh::lean_ctor_get(v___x_2157_, 5);
                v_messages_2165_ = crate::leanh::lean_ctor_get(v___x_2157_, 6);
                v_snapshotTasks_2166_ = crate::leanh::lean_ctor_get(v___x_2157_, 8);
                v_isSharedCheck_2190_ = (!crate::leanh::lean_is_exclusive(v___x_2157_)) as u8;
                if v_isSharedCheck_2190_ == 0 {
                    v___x_2168_ = v___x_2157_;
                    v_isShared_2169_ = v_isSharedCheck_2190_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2166_);
                    crate::leanh::lean_inc(v_infoState_2158_);
                    crate::leanh::lean_inc(v_messages_2165_);
                    crate::leanh::lean_inc(v_cache_2164_);
                    crate::leanh::lean_inc(v_traceState_2163_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2162_);
                    crate::leanh::lean_inc(v_ngen_2161_);
                    crate::leanh::lean_inc(v_nextMacroScope_2160_);
                    crate::leanh::lean_inc(v_env_2159_);
                    crate::leanh::lean_dec(v___x_2157_);
                    v___x_2168_ = crate::leanh::lean_box(0);
                    v_isShared_2169_ = v_isSharedCheck_2190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_2170_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2158_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_2171_ = crate::leanh::lean_ctor_get(v_infoState_2158_, 0);
                v_lazyAssignment_2172_ = crate::leanh::lean_ctor_get(v_infoState_2158_, 1);
                v_isSharedCheck_2188_ = (!crate::leanh::lean_is_exclusive(v_infoState_2158_)) as u8;
                if v_isSharedCheck_2188_ == 0 {
                    v_unused_2189_ = crate::leanh::lean_ctor_get(v_infoState_2158_, 2);
                    crate::leanh::lean_dec(v_unused_2189_);
                    v___x_2174_ = v_infoState_2158_;
                    v_isShared_2175_ = v_isSharedCheck_2188_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_2172_);
                    crate::leanh::lean_inc(v_assignment_2171_);
                    crate::leanh::lean_dec(v_infoState_2158_);
                    v___x_2174_ = crate::leanh::lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2176_ = l_Lean_PersistentArray_append___redArg(v_a_2146_, v_a_2153_);
                crate::leanh::lean_dec(v_a_2153_);
                if v_isShared_2175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2174_, 2, v___x_2176_);
                    v___x_2178_ = v___x_2174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_assignment_2171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_lazyAssignment_2172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2176_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2187_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_2170_,
                    );
                    v___x_2178_ = v_reuseFailAlloc_2187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2168_, 7, v___x_2178_);
                    v___x_2180_ = v___x_2168_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_env_2159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_nextMacroScope_2160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_ngen_2161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_auxDeclNGen_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_traceState_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 5, v_cache_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 6, v_messages_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 7, v___x_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 8, v_snapshotTasks_2166_);
                    v___x_2180_ = v_reuseFailAlloc_2186_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2181_ = lean_st_ref_set(v___y_2139_, v___x_2180_);
                v___x_2182_ = crate::leanh::lean_box(0);
                if v_isShared_2156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2182_);
                    v___x_2184_ = v___x_2155_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2184_;
            }
            7 => {
                if v_isShared_2195_ == 0 {
                    v___x_2197_ = v___x_2194_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0___boxed(
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2200_, v_ctx_x3f_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v_a_2207_, v_a_x3f_2208_);
    crate::leanh::lean_dec(v_a_x3f_2208_);
    crate::leanh::lean_dec_ref(v___y_2206_);
    crate::leanh::lean_dec(v___y_2205_);
    crate::leanh::lean_dec_ref(v___y_2204_);
    crate::leanh::lean_dec(v___y_2203_);
    crate::leanh::lean_dec_ref(v___y_2202_);
    crate::leanh::lean_dec(v___y_2200_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_unused_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_unused_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_st_ref_get(v___y_2218_);
                v_infoState_2221_ = crate::leanh::lean_ctor_get(v___x_2220_, 7);
                crate::leanh::lean_inc_ref(v_infoState_2221_);
                crate::leanh::lean_dec(v___x_2220_);
                v_enabled_2222_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_2221_);
                if v_enabled_2222_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_2212_);
                    crate::leanh::lean_inc(v___y_2218_);
                    crate::leanh::lean_inc_ref(v___y_2217_);
                    crate::leanh::lean_inc(v___y_2216_);
                    crate::leanh::lean_inc_ref(v___y_2215_);
                    crate::leanh::lean_inc(v___y_2214_);
                    crate::leanh::lean_inc_ref(v___y_2213_);
                    v___x_2223_ = crate::leanh::lean_apply_7(
                        v_x_2211_,
                        v___y_2213_,
                        v___y_2214_,
                        v___y_2215_,
                        v___y_2216_,
                        v___y_2217_,
                        v___y_2218_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2223_;
                } else {
                    v___x_2224_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_2218_);
                    v_a_2225_ = crate::leanh::lean_ctor_get(v___x_2224_, 0);
                    crate::leanh::lean_inc(v_a_2225_);
                    crate::leanh::lean_dec_ref(v___x_2224_);
                    crate::leanh::lean_inc(v___y_2218_);
                    crate::leanh::lean_inc_ref(v___y_2217_);
                    crate::leanh::lean_inc(v___y_2216_);
                    crate::leanh::lean_inc_ref(v___y_2215_);
                    crate::leanh::lean_inc(v___y_2214_);
                    crate::leanh::lean_inc_ref(v___y_2213_);
                    v_r_2226_ = crate::leanh::lean_apply_7(
                        v_x_2211_,
                        v___y_2213_,
                        v___y_2214_,
                        v___y_2215_,
                        v___y_2216_,
                        v___y_2217_,
                        v___y_2218_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_2226_) == 0 {
                        v_a_2227_ = crate::leanh::lean_ctor_get(v_r_2226_, 0);
                        v_isSharedCheck_2251_ = (!crate::leanh::lean_is_exclusive(v_r_2226_)) as u8;
                        if v_isSharedCheck_2251_ == 0 {
                            v___x_2229_ = v_r_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2227_);
                            crate::leanh::lean_dec(v_r_2226_);
                            v___x_2229_ = crate::leanh::lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2252_ = crate::leanh::lean_ctor_get(v_r_2226_, 0);
                        crate::leanh::lean_inc(v_a_2252_);
                        crate::leanh::lean_dec_ref_known(v_r_2226_, 1);
                        v___x_2253_ = crate::leanh::lean_box(0);
                        v___x_2254_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2218_, v_ctx_x3f_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v_a_2225_, v___x_2253_);
                        if crate::leanh::lean_obj_tag(v___x_2254_) == 0 {
                            v_isSharedCheck_2261_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                            if v_isSharedCheck_2261_ == 0 {
                                v_unused_2262_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                                crate::leanh::lean_dec(v_unused_2262_);
                                v___x_2256_ = v___x_2254_;
                                v_isShared_2257_ = v_isSharedCheck_2261_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2254_);
                                v___x_2256_ = crate::leanh::lean_box(0);
                                v_isShared_2257_ = v_isSharedCheck_2261_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2252_);
                            v_a_2263_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                            v_isSharedCheck_2270_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                            if v_isSharedCheck_2270_ == 0 {
                                v___x_2265_ = v___x_2254_;
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2263_);
                                crate::leanh::lean_dec(v___x_2254_);
                                v___x_2265_ = crate::leanh::lean_box(0);
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2227_);
                if v_isShared_2230_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2229_, 1);
                    v___x_2232_ = v___x_2229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2227_);
                    v___x_2232_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2233_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2218_, v_ctx_x3f_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v_a_2225_, v___x_2232_);
                crate::leanh::lean_dec_ref(v___x_2232_);
                if crate::leanh::lean_obj_tag(v___x_2233_) == 0 {
                    v_isSharedCheck_2240_ = (!crate::leanh::lean_is_exclusive(v___x_2233_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v_unused_2241_ = crate::leanh::lean_ctor_get(v___x_2233_, 0);
                        crate::leanh::lean_dec(v_unused_2241_);
                        v___x_2235_ = v___x_2233_;
                        v_isShared_2236_ = v_isSharedCheck_2240_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2233_);
                        v___x_2235_ = crate::leanh::lean_box(0);
                        v_isShared_2236_ = v_isSharedCheck_2240_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2227_);
                    v_a_2242_ = crate::leanh::lean_ctor_get(v___x_2233_, 0);
                    v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v___x_2233_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v___x_2233_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2242_);
                        crate::leanh::lean_dec(v___x_2233_);
                        v___x_2244_ = crate::leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2235_, 0, v_a_2227_);
                    v___x_2238_ = v___x_2235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2227_);
                    v___x_2238_ = v_reuseFailAlloc_2239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2238_;
            }
            5 => {
                if v_isShared_2245_ == 0 {
                    v___x_2247_ = v___x_2244_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
                    v___x_2247_ = v_reuseFailAlloc_2248_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2247_;
            }
            7 => {
                if v_isShared_2257_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2256_, 1);
                    crate::leanh::lean_ctor_set(v___x_2256_, 0, v_a_2252_);
                    v___x_2259_ = v___x_2256_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2252_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2259_;
            }
            9 => {
                if v_isShared_2266_ == 0 {
                    v___x_2268_ = v___x_2265_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___boxed(
    mut v_x_2271_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_2271_, v_ctx_x3f_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
    crate::leanh::lean_dec(v___y_2278_);
    crate::leanh::lean_dec_ref(v___y_2277_);
    crate::leanh::lean_dec(v___y_2276_);
    crate::leanh::lean_dec_ref(v___y_2275_);
    crate::leanh::lean_dec(v___y_2274_);
    crate::leanh::lean_dec_ref(v___y_2273_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = lean_st_ref_get(v___y_2283_);
    v_env_2286_ = crate::leanh::lean_ctor_get(v___x_2285_, 0);
    crate::leanh::lean_inc_ref(v_env_2286_);
    crate::leanh::lean_dec(v___x_2285_);
    v___x_2287_ = lean_st_ref_get(v___y_2281_);
    v_mctx_2288_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2288_);
    crate::leanh::lean_dec(v___x_2287_);
    v_options_2289_ = crate::leanh::lean_ctor_get(v___y_2282_, 2);
    v_currNamespace_2290_ = crate::leanh::lean_ctor_get(v___y_2282_, 6);
    v_openDecls_2291_ = crate::leanh::lean_ctor_get(v___y_2282_, 7);
    v___x_2292_ = lean_st_ref_get(v___y_2283_);
    v_ngen_2293_ = crate::leanh::lean_ctor_get(v___x_2292_, 2);
    crate::leanh::lean_inc_ref(v_ngen_2293_);
    crate::leanh::lean_dec(v___x_2292_);
    v___x_2294_ = crate::leanh::lean_box(0);
    v___x_2295_ = l_Lean_instInhabitedFileMap_default;
    crate::leanh::lean_inc(v_openDecls_2291_);
    crate::leanh::lean_inc(v_currNamespace_2290_);
    crate::leanh::lean_inc_ref(v_options_2289_);
    v___x_2296_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2296_, 0, v_env_2286_);
    crate::leanh::lean_ctor_set(v___x_2296_, 1, v___x_2294_);
    crate::leanh::lean_ctor_set(v___x_2296_, 2, v___x_2295_);
    crate::leanh::lean_ctor_set(v___x_2296_, 3, v_mctx_2288_);
    crate::leanh::lean_ctor_set(v___x_2296_, 4, v_options_2289_);
    crate::leanh::lean_ctor_set(v___x_2296_, 5, v_currNamespace_2290_);
    crate::leanh::lean_ctor_set(v___x_2296_, 6, v_openDecls_2291_);
    crate::leanh::lean_ctor_set(v___x_2296_, 7, v_ngen_2293_);
    v___x_2297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2297_, 0, v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_2298_, v___y_2299_, v___y_2300_);
    crate::leanh::lean_dec(v___y_2300_);
    crate::leanh::lean_dec_ref(v___y_2299_);
    crate::leanh::lean_dec(v___y_2298_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v_fileMap_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut v_unused_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2310_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_2306_, v___y_2307_, v___y_2308_);
                v_a_2311_ = crate::leanh::lean_ctor_get(v___x_2310_, 0);
                v_isSharedCheck_2335_ = (!crate::leanh::lean_is_exclusive(v___x_2310_)) as u8;
                if v_isSharedCheck_2335_ == 0 {
                    v___x_2313_ = v___x_2310_;
                    v_isShared_2314_ = v_isSharedCheck_2335_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2311_);
                    crate::leanh::lean_dec(v___x_2310_);
                    v___x_2313_ = crate::leanh::lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2335_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_2315_ = crate::leanh::lean_ctor_get(v___y_2307_, 1);
                v_env_2316_ = crate::leanh::lean_ctor_get(v_a_2311_, 0);
                v_mctx_2317_ = crate::leanh::lean_ctor_get(v_a_2311_, 3);
                v_options_2318_ = crate::leanh::lean_ctor_get(v_a_2311_, 4);
                v_currNamespace_2319_ = crate::leanh::lean_ctor_get(v_a_2311_, 5);
                v_openDecls_2320_ = crate::leanh::lean_ctor_get(v_a_2311_, 6);
                v_ngen_2321_ = crate::leanh::lean_ctor_get(v_a_2311_, 7);
                v_isSharedCheck_2332_ = (!crate::leanh::lean_is_exclusive(v_a_2311_)) as u8;
                if v_isSharedCheck_2332_ == 0 {
                    v_unused_2333_ = crate::leanh::lean_ctor_get(v_a_2311_, 2);
                    crate::leanh::lean_dec(v_unused_2333_);
                    v_unused_2334_ = crate::leanh::lean_ctor_get(v_a_2311_, 1);
                    crate::leanh::lean_dec(v_unused_2334_);
                    v___x_2323_ = v_a_2311_;
                    v_isShared_2324_ = v_isSharedCheck_2332_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_2321_);
                    crate::leanh::lean_inc(v_openDecls_2320_);
                    crate::leanh::lean_inc(v_currNamespace_2319_);
                    crate::leanh::lean_inc(v_options_2318_);
                    crate::leanh::lean_inc(v_mctx_2317_);
                    crate::leanh::lean_inc(v_env_2316_);
                    crate::leanh::lean_dec(v_a_2311_);
                    v___x_2323_ = crate::leanh::lean_box(0);
                    v_isShared_2324_ = v_isSharedCheck_2332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2325_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_fileMap_2315_);
                if v_isShared_2324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2323_, 2, v_fileMap_2315_);
                    crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2325_);
                    v___x_2327_ = v___x_2323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2331_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_env_2316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_fileMap_2315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_mctx_2317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_options_2318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 5, v_currNamespace_2319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 6, v_openDecls_2320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 7, v_ngen_2321_);
                    v___x_2327_ = v_reuseFailAlloc_2331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2327_);
                    v___x_2329_ = v___x_2313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2___boxed(
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    crate::leanh::lean_dec(v___y_2341_);
    crate::leanh::lean_dec_ref(v___y_2340_);
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v___y_2338_);
    crate::leanh::lean_dec(v___y_2337_);
    crate::leanh::lean_dec_ref(v___y_2336_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
                v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                v_isSharedCheck_2361_ = (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                if v_isSharedCheck_2361_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    v_isShared_2355_ = v_isSharedCheck_2361_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2352_);
                    crate::leanh::lean_dec(v___x_2351_);
                    v___x_2354_ = crate::leanh::lean_box(0);
                    v_isShared_2355_ = v_isSharedCheck_2361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2356_, 0, v_a_2352_);
                v___x_2357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2356_);
                if v_isShared_2355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2357_);
                    v___x_2359_ = v___x_2354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
                    v___x_2359_ = v_reuseFailAlloc_2360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed(
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
    crate::leanh::lean_dec(v___y_2367_);
    crate::leanh::lean_dec_ref(v___y_2366_);
    crate::leanh::lean_dec(v___y_2365_);
    crate::leanh::lean_dec_ref(v___y_2364_);
    crate::leanh::lean_dec(v___y_2363_);
    crate::leanh::lean_dec_ref(v___y_2362_);
    return v_res_2369_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(
    mut v_x_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2379_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0;
    v___x_2380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_2371_, v___f_2379_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
    return v___x_2380_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(
    mut v_x_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
    crate::leanh::lean_dec(v___y_2387_);
    crate::leanh::lean_dec_ref(v___y_2386_);
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    return v_res_2389_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(
    mut v_snd_2390_: *mut crate::leanh::LeanObject,
    mut v___x_2391_: *mut crate::leanh::LeanObject,
    mut v_____r_2392_: *mut crate::leanh::LeanObject,
    mut v_lctx_2393_: *mut crate::leanh::LeanObject,
    mut v_hs_2394_: *mut crate::leanh::LeanObject,
    mut v_info_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_NameSet_insert(v_snd_2390_, v___x_2391_);
    v___x_2404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2404_, 0, v_info_2395_);
    crate::leanh::lean_ctor_set(v___x_2404_, 1, v___x_2403_);
    v___x_2405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2405_, 0, v_hs_2394_);
    crate::leanh::lean_ctor_set(v___x_2405_, 1, v___x_2404_);
    v___x_2406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2406_, 0, v_lctx_2393_);
    crate::leanh::lean_ctor_set(v___x_2406_, 1, v___x_2405_);
    v___x_2407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2407_, 0, v___x_2406_);
    v___x_2408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
    return v___x_2408_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(
    mut v_snd_2409_: *mut crate::leanh::LeanObject,
    mut v___x_2410_: *mut crate::leanh::LeanObject,
    mut v_____r_2411_: *mut crate::leanh::LeanObject,
    mut v_lctx_2412_: *mut crate::leanh::LeanObject,
    mut v_hs_2413_: *mut crate::leanh::LeanObject,
    mut v_info_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_2409_, v___x_2410_, v_____r_2411_, v_lctx_2412_, v_hs_2413_, v_info_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
    crate::leanh::lean_dec(v___y_2420_);
    crate::leanh::lean_dec_ref(v___y_2419_);
    crate::leanh::lean_dec(v___y_2418_);
    crate::leanh::lean_dec_ref(v___y_2417_);
    crate::leanh::lean_dec(v___y_2416_);
    crate::leanh::lean_dec_ref(v___y_2415_);
    return v_res_2422_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(
    mut v_fst_2423_: *mut crate::leanh::LeanObject,
    mut v___f_2424_: *mut crate::leanh::LeanObject,
    mut v_snd_2425_: *mut crate::leanh::LeanObject,
    mut v_____r_2426_: *mut crate::leanh::LeanObject,
    mut v_lctx_2427_: *mut crate::leanh::LeanObject,
    mut v_info_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    v___x_2436_ = lean_array_pop(v_fst_2423_);
    v___x_2437_ = lean_array_get_size(v___x_2436_);
    v___x_2438_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2439_ = lean_nat_dec_eq(v___x_2437_, v___x_2438_);
    if v___x_2439_ == 0 {
        let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_snd_2425_);
        v___x_2440_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v___y_2434_);
        crate::leanh::lean_inc_ref(v___y_2433_);
        crate::leanh::lean_inc(v___y_2432_);
        crate::leanh::lean_inc_ref(v___y_2431_);
        crate::leanh::lean_inc(v___y_2430_);
        crate::leanh::lean_inc_ref(v___y_2429_);
        v___x_2441_ = crate::leanh::lean_apply_11(
            v___f_2424_,
            v___x_2440_,
            v_lctx_2427_,
            v___x_2436_,
            v_info_2428_,
            v___y_2429_,
            v___y_2430_,
            v___y_2431_,
            v___y_2432_,
            v___y_2433_,
            v___y_2434_,
            crate::leanh::lean_box(0),
        );
        return v___x_2441_;
    } else {
        let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_2424_);
        v___x_2442_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2442_, 0, v_info_2428_);
        crate::leanh::lean_ctor_set(v___x_2442_, 1, v_snd_2425_);
        v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2436_);
        crate::leanh::lean_ctor_set(v___x_2443_, 1, v___x_2442_);
        v___x_2444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2444_, 0, v_lctx_2427_);
        crate::leanh::lean_ctor_set(v___x_2444_, 1, v___x_2443_);
        v___x_2445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2445_, 0, v___x_2444_);
        v___x_2446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2446_, 0, v___x_2445_);
        return v___x_2446_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(
    mut v_fst_2447_: *mut crate::leanh::LeanObject,
    mut v___f_2448_: *mut crate::leanh::LeanObject,
    mut v_snd_2449_: *mut crate::leanh::LeanObject,
    mut v_____r_2450_: *mut crate::leanh::LeanObject,
    mut v_lctx_2451_: *mut crate::leanh::LeanObject,
    mut v_info_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2447_, v___f_2448_, v_snd_2449_, v_____r_2450_, v_lctx_2451_, v_info_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
    crate::leanh::lean_dec(v___y_2458_);
    crate::leanh::lean_dec_ref(v___y_2457_);
    crate::leanh::lean_dec(v___y_2456_);
    crate::leanh::lean_dec_ref(v___y_2455_);
    crate::leanh::lean_dec(v___y_2454_);
    crate::leanh::lean_dec_ref(v___y_2453_);
    return v_res_2460_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(
    mut v_upperBound_2469_: *mut crate::leanh::LeanObject,
    mut v___x_2470_: *mut crate::leanh::LeanObject,
    mut v_val_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
    mut v_b_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_a_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v_fst_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v_fst_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_unused_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v_unused_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2506_ = lean_nat_dec_lt(v_a_2472_, v_upperBound_2469_);
                if v___x_2506_ == 0 {
                    crate::leanh::lean_dec(v_a_2472_);
                    v___x_2507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2507_, 0, v_b_2473_);
                    return v___x_2507_;
                } else {
                    v_snd_2508_ = crate::leanh::lean_ctor_get(v_b_2473_, 1);
                    crate::leanh::lean_inc(v_snd_2508_);
                    v_snd_2509_ = crate::leanh::lean_ctor_get(v_snd_2508_, 1);
                    crate::leanh::lean_inc(v_snd_2509_);
                    v_fst_2510_ = crate::leanh::lean_ctor_get(v_b_2473_, 0);
                    v_isSharedCheck_2581_ = (!crate::leanh::lean_is_exclusive(v_b_2473_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v_unused_2582_ = crate::leanh::lean_ctor_get(v_b_2473_, 1);
                        crate::leanh::lean_dec(v_unused_2582_);
                        v___x_2512_ = v_b_2473_;
                        v_isShared_2513_ = v_isSharedCheck_2581_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2510_);
                        crate::leanh::lean_dec(v_b_2473_);
                        v___x_2512_ = crate::leanh::lean_box(0);
                        v_isShared_2513_ = v_isSharedCheck_2581_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2483_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2484_ = lean_nat_add(v_a_2472_, v___x_2483_);
                crate::leanh::lean_dec(v_a_2472_);
                v_a_2472_ = v___x_2484_;
                v_b_2473_ = v_a_2482_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2487_) == 0 {
                    v_a_2488_ = crate::leanh::lean_ctor_get(v___y_2487_, 0);
                    v_isSharedCheck_2497_ = (!crate::leanh::lean_is_exclusive(v___y_2487_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v___x_2490_ = v___y_2487_;
                        v_isShared_2491_ = v_isSharedCheck_2497_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2488_);
                        crate::leanh::lean_dec(v___y_2487_);
                        v___x_2490_ = crate::leanh::lean_box(0);
                        v_isShared_2491_ = v_isSharedCheck_2497_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2472_);
                    v_a_2498_ = crate::leanh::lean_ctor_get(v___y_2487_, 0);
                    v_isSharedCheck_2505_ = (!crate::leanh::lean_is_exclusive(v___y_2487_)) as u8;
                    if v_isSharedCheck_2505_ == 0 {
                        v___x_2500_ = v___y_2487_;
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2498_);
                        crate::leanh::lean_dec(v___y_2487_);
                        v___x_2500_ = crate::leanh::lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2488_) == 0 {
                    crate::leanh::lean_dec(v_a_2472_);
                    v_a_2492_ = crate::leanh::lean_ctor_get(v_a_2488_, 0);
                    crate::leanh::lean_inc(v_a_2492_);
                    crate::leanh::lean_dec_ref_known(v_a_2488_, 1);
                    if v_isShared_2491_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2490_, 0, v_a_2492_);
                        v___x_2494_ = v___x_2490_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2492_);
                        v___x_2494_ = v_reuseFailAlloc_2495_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2490_);
                    v_a_2496_ = crate::leanh::lean_ctor_get(v_a_2488_, 0);
                    crate::leanh::lean_inc(v_a_2496_);
                    crate::leanh::lean_dec_ref_known(v_a_2488_, 1);
                    v_a_2482_ = v_a_2496_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_2494_;
            }
            5 => {
                if v_isShared_2501_ == 0 {
                    v___x_2503_ = v___x_2500_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
                    v___x_2503_ = v_reuseFailAlloc_2504_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2503_;
            }
            7 => {
                v_fst_2514_ = crate::leanh::lean_ctor_get(v_snd_2508_, 0);
                v_isSharedCheck_2579_ = (!crate::leanh::lean_is_exclusive(v_snd_2508_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v_unused_2580_ = crate::leanh::lean_ctor_get(v_snd_2508_, 1);
                    crate::leanh::lean_dec(v_unused_2580_);
                    v___x_2516_ = v_snd_2508_;
                    v_isShared_2517_ = v_isSharedCheck_2579_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2514_);
                    crate::leanh::lean_dec(v_snd_2508_);
                    v___x_2516_ = crate::leanh::lean_box(0);
                    v_isShared_2517_ = v_isSharedCheck_2579_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_2518_ = crate::leanh::lean_ctor_get(v_snd_2509_, 0);
                v_snd_2519_ = crate::leanh::lean_ctor_get(v_snd_2509_, 1);
                v_isSharedCheck_2578_ = (!crate::leanh::lean_is_exclusive(v_snd_2509_)) as u8;
                if v_isSharedCheck_2578_ == 0 {
                    v___x_2521_ = v_snd_2509_;
                    v_isShared_2522_ = v_isSharedCheck_2578_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2519_);
                    crate::leanh::lean_inc(v_fst_2518_);
                    crate::leanh::lean_dec(v_snd_2509_);
                    v___x_2521_ = crate::leanh::lean_box(0);
                    v_isShared_2522_ = v_isSharedCheck_2578_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2523_ = lean_nat_sub(v___x_2470_, v_a_2472_);
                v___x_2524_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2525_ = lean_nat_sub(v___x_2523_, v___x_2524_);
                crate::leanh::lean_dec(v___x_2523_);
                v___x_2526_ = l_Lean_LocalContext_getAt_x3f(v_fst_2510_, v___x_2525_);
                crate::leanh::lean_dec(v___x_2525_);
                if crate::leanh::lean_obj_tag(v___x_2526_) == 0 {
                    if v_isShared_2522_ == 0 {
                        v___x_2528_ = v___x_2521_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_fst_2518_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_snd_2519_);
                        v___x_2528_ = v_reuseFailAlloc_2535_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_val_2536_ = crate::leanh::lean_ctor_get(v___x_2526_, 0);
                    crate::leanh::lean_inc(v_val_2536_);
                    crate::leanh::lean_dec_ref_known(v___x_2526_, 1);
                    v___x_2537_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2536_);
                    if v___x_2537_ == 0 {
                        crate::leanh::lean_del_object(v___x_2516_);
                        crate::leanh::lean_del_object(v___x_2512_);
                        v___x_2538_ = l_Lean_LocalDecl_userName(v_val_2536_);
                        crate::leanh::lean_inc_n(v___x_2538_, 2);
                        crate::leanh::lean_inc(v_snd_2519_);
                        v___f_2539_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                        crate::leanh::lean_closure_set(v___f_2539_, 0, v_snd_2519_);
                        crate::leanh::lean_closure_set(v___f_2539_, 1, v___x_2538_);
                        v___x_2564_ = l_Lean_extractMacroScopes(v___x_2538_);
                        v___x_2565_ = l_Lean_MacroScopesView_equalScope(v___x_2564_, v_val_2471_);
                        crate::leanh::lean_dec_ref(v___x_2564_);
                        if v___x_2565_ == 0 {
                            crate::leanh::lean_dec(v___x_2538_);
                            state = 13;
                            continue;
                        } else {
                            if v___x_2537_ == 0 {
                                v___x_2566_ = l_Lean_NameSet_contains(v_snd_2519_, v___x_2538_);
                                if v___x_2566_ == 0 {
                                    crate::leanh::lean_dec_ref(v___f_2539_);
                                    crate::leanh::lean_dec(v_val_2536_);
                                    crate::leanh::lean_del_object(v___x_2521_);
                                    v___x_2567_ = crate::leanh::lean_box(0);
                                    v___x_2568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_2519_, v___x_2538_, v___x_2567_, v_fst_2510_, v_fst_2514_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                                    v___y_2487_ = v___x_2568_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2538_);
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2538_);
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2536_);
                        if v_isShared_2522_ == 0 {
                            v___x_2570_ = v___x_2521_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_2577_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_fst_2518_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2519_);
                            v___x_2570_ = v_reuseFailAlloc_2577_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_2517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2516_, 1, v___x_2528_);
                    v___x_2530_ = v___x_2516_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_fst_2514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2534_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2512_, 1, v___x_2530_);
                    v___x_2532_ = v___x_2512_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fst_2510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_a_2482_ = v___x_2532_;
                state = 1;
                continue;
            }
            13 => {
                v___x_2541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2;
                v___x_2542_ = crate::leanh::lean_box(0);
                v___x_2543_ = lean_array_get_size(v_fst_2514_);
                v___x_2544_ = lean_nat_sub(v___x_2543_, v___x_2524_);
                v___x_2545_ = lean_array_get_borrowed(v___x_2542_, v_fst_2514_, v___x_2544_);
                crate::leanh::lean_dec(v___x_2544_);
                crate::leanh::lean_inc(v___x_2545_);
                v___x_2546_ = l_Lean_Syntax_isOfKind(v___x_2545_, v___x_2541_);
                if v___x_2546_ == 0 {
                    crate::leanh::lean_dec(v_val_2536_);
                    crate::leanh::lean_del_object(v___x_2521_);
                    v___x_2547_ = crate::leanh::lean_box(0);
                    v___x_2548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2547_, v_fst_2510_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                    v___y_2487_ = v___x_2548_;
                    state = 2;
                    continue;
                } else {
                    v___x_2549_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2550_ = l_Lean_Syntax_getArg(v___x_2545_, v___x_2549_);
                    v___x_2551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4;
                    crate::leanh::lean_inc(v___x_2550_);
                    v___x_2552_ = l_Lean_Syntax_isOfKind(v___x_2550_, v___x_2551_);
                    if v___x_2552_ == 0 {
                        crate::leanh::lean_dec(v___x_2550_);
                        crate::leanh::lean_dec(v_val_2536_);
                        crate::leanh::lean_del_object(v___x_2521_);
                        v___x_2553_ = crate::leanh::lean_box(0);
                        v___x_2554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2553_, v_fst_2510_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                        v___y_2487_ = v___x_2554_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2555_ = l_Lean_TSyntax_getId(v___x_2550_);
                        v___x_2556_ = l_Lean_LocalDecl_fvarId(v_val_2536_);
                        crate::leanh::lean_dec(v_val_2536_);
                        crate::leanh::lean_inc(v___x_2556_);
                        v___x_2557_ =
                            l_Lean_LocalContext_setUserName(v_fst_2510_, v___x_2556_, v___x_2555_);
                        if v_isShared_2522_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2521_, 1, v___x_2550_);
                            crate::leanh::lean_ctor_set(v___x_2521_, 0, v___x_2556_);
                            v___x_2559_ = v___x_2521_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2563_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2556_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2550_);
                            v___x_2559_ = v_reuseFailAlloc_2563_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                v___x_2560_ = lean_array_push(v_fst_2518_, v___x_2559_);
                v___x_2561_ = crate::leanh::lean_box(0);
                v___x_2562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2561_, v___x_2557_, v___x_2560_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                v___y_2487_ = v___x_2562_;
                state = 2;
                continue;
            }
            15 => {
                if v_isShared_2517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2516_, 1, v___x_2570_);
                    v___x_2572_ = v___x_2516_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2570_);
                    v___x_2572_ = v_reuseFailAlloc_2576_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2512_, 1, v___x_2572_);
                    v___x_2574_ = v___x_2512_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2572_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v_a_2482_ = v___x_2574_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___boxed(
    mut v_upperBound_2583_: *mut crate::leanh::LeanObject,
    mut v___x_2584_: *mut crate::leanh::LeanObject,
    mut v_val_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_b_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_2583_, v___x_2584_, v_val_2585_, v_a_2586_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
    crate::leanh::lean_dec(v___y_2593_);
    crate::leanh::lean_dec_ref(v___y_2592_);
    crate::leanh::lean_dec(v___y_2591_);
    crate::leanh::lean_dec_ref(v___y_2590_);
    crate::leanh::lean_dec(v___y_2589_);
    crate::leanh::lean_dec_ref(v___y_2588_);
    crate::leanh::lean_dec_ref(v_val_2585_);
    crate::leanh::lean_dec(v___x_2584_);
    crate::leanh::lean_dec(v_upperBound_2583_);
    return v_res_2595_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(
    mut v___y_2604_: u8,
    mut v_suppressElabErrors_2605_: u8,
    mut v_x_2606_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2606_) == 1 {
        let mut v_pre_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2607_ = crate::leanh::lean_ctor_get(v_x_2606_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2607_) {
            1 => {
                let mut v_pre_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2608_ = crate::leanh::lean_ctor_get(v_pre_2607_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2608_) {
                    0 => {
                        let mut v_str_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2612_: u8 = 0;
                        v_str_2609_ = crate::leanh::lean_ctor_get(v_x_2606_, 1);
                        v_str_2610_ = crate::leanh::lean_ctor_get(v_pre_2607_, 1);
                        v___x_2611_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0;
                        v___x_2612_ = lean_string_dec_eq(v_str_2610_, v___x_2611_);
                        if v___x_2612_ == 0 {
                            let mut v___x_2613_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2614_: u8 = 0;
                            v___x_2613_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1;
                            v___x_2614_ = lean_string_dec_eq(v_str_2610_, v___x_2613_);
                            if v___x_2614_ == 0 {
                                return v___y_2604_;
                            } else {
                                let mut v___x_2615_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2616_: u8 = 0;
                                v___x_2615_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2;
                                v___x_2616_ = lean_string_dec_eq(v_str_2609_, v___x_2615_);
                                if v___x_2616_ == 0 {
                                    return v___y_2604_;
                                } else {
                                    return v_suppressElabErrors_2605_;
                                }
                            }
                        } else {
                            let mut v___x_2617_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2618_: u8 = 0;
                            v___x_2617_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3;
                            v___x_2618_ = lean_string_dec_eq(v_str_2609_, v___x_2617_);
                            if v___x_2618_ == 0 {
                                return v___y_2604_;
                            } else {
                                return v_suppressElabErrors_2605_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2619_ = crate::leanh::lean_ctor_get(v_pre_2608_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2619_) == 0 {
                            let mut v_str_2620_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2621_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2622_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2623_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2624_: u8 = 0;
                            v_str_2620_ = crate::leanh::lean_ctor_get(v_x_2606_, 1);
                            v_str_2621_ = crate::leanh::lean_ctor_get(v_pre_2607_, 1);
                            v_str_2622_ = crate::leanh::lean_ctor_get(v_pre_2608_, 1);
                            v___x_2623_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4;
                            v___x_2624_ = lean_string_dec_eq(v_str_2622_, v___x_2623_);
                            if v___x_2624_ == 0 {
                                return v___y_2604_;
                            } else {
                                let mut v___x_2625_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2626_: u8 = 0;
                                v___x_2625_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5;
                                v___x_2626_ = lean_string_dec_eq(v_str_2621_, v___x_2625_);
                                if v___x_2626_ == 0 {
                                    return v___y_2604_;
                                } else {
                                    let mut v___x_2627_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2628_: u8 = 0;
                                    v___x_2627_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6;
                                    v___x_2628_ = lean_string_dec_eq(v_str_2620_, v___x_2627_);
                                    if v___x_2628_ == 0 {
                                        return v___y_2604_;
                                    } else {
                                        return v_suppressElabErrors_2605_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2604_;
                        }
                    }
                    _ => {
                        return v___y_2604_;
                    }
                }
            }
            0 => {
                let mut v_str_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2631_: u8 = 0;
                v_str_2629_ = crate::leanh::lean_ctor_get(v_x_2606_, 1);
                v___x_2630_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7;
                v___x_2631_ = lean_string_dec_eq(v_str_2629_, v___x_2630_);
                if v___x_2631_ == 0 {
                    return v___y_2604_;
                } else {
                    return v_suppressElabErrors_2605_;
                }
            }
            _ => {
                return v___y_2604_;
            }
        }
    } else {
        return v___y_2604_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed(
    mut v___y_2632_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2633_: *mut crate::leanh::LeanObject,
    mut v_x_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23688__boxed_2635_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2636_: u8 = 0;
    let mut v_res_2637_: u8 = 0;
    let mut v_r_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23688__boxed_2635_ = (crate::leanh::lean_unbox(v___y_2632_) as u8);
    v_suppressElabErrors_boxed_2636_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2633_) as u8);
    v_res_2637_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v___y_23688__boxed_2635_, v_suppressElabErrors_boxed_2636_, v_x_2634_);
    crate::leanh::lean_dec(v_x_2634_);
    v_r_2638_ = crate::leanh::lean_box((v_res_2637_) as usize);
    return v_r_2638_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(
    mut v_opts_2639_: *mut crate::leanh::LeanObject,
    mut v_opt_2640_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2641_ = crate::leanh::lean_ctor_get(v_opt_2640_, 0);
    v_defValue_2642_ = crate::leanh::lean_ctor_get(v_opt_2640_, 1);
    v_map_2643_ = crate::leanh::lean_ctor_get(v_opts_2639_, 0);
    v___x_2644_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2643_,
            v_name_2641_,
        );
    if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
        let mut v___x_2645_: u8 = 0;
        v___x_2645_ = (crate::leanh::lean_unbox(v_defValue_2642_) as u8);
        return v___x_2645_;
    } else {
        let mut v_val_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2646_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
        crate::leanh::lean_inc(v_val_2646_);
        crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
        if crate::leanh::lean_obj_tag(v_val_2646_) == 1 {
            let mut v_v_2647_: u8 = 0;
            v_v_2647_ = crate::leanh::lean_ctor_get_uint8(v_val_2646_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2646_, 0);
            return v_v_2647_;
        } else {
            let mut v___x_2648_: u8 = 0;
            crate::leanh::lean_dec(v_val_2646_);
            v___x_2648_ = (crate::leanh::lean_unbox(v_defValue_2642_) as u8);
            return v___x_2648_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(
    mut v_opts_2649_: *mut crate::leanh::LeanObject,
    mut v_opt_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: u8 = 0;
    let mut v_r_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_2649_, v_opt_2650_);
    crate::leanh::lean_dec_ref(v_opt_2650_);
    crate::leanh::lean_dec_ref(v_opts_2649_);
    v_r_2652_ = crate::leanh::lean_box((v_res_2651_) as usize);
    return v_r_2652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(
    mut v_msgData_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = lean_st_ref_get(v___y_2657_);
    v_env_2660_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
    crate::leanh::lean_inc_ref(v_env_2660_);
    crate::leanh::lean_dec(v___x_2659_);
    v___x_2661_ = lean_st_ref_get(v___y_2655_);
    v_mctx_2662_ = crate::leanh::lean_ctor_get(v___x_2661_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2662_);
    crate::leanh::lean_dec(v___x_2661_);
    v_lctx_2663_ = crate::leanh::lean_ctor_get(v___y_2654_, 2);
    v_options_2664_ = crate::leanh::lean_ctor_get(v___y_2656_, 2);
    crate::leanh::lean_inc_ref(v_options_2664_);
    crate::leanh::lean_inc_ref(v_lctx_2663_);
    v___x_2665_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2665_, 0, v_env_2660_);
    crate::leanh::lean_ctor_set(v___x_2665_, 1, v_mctx_2662_);
    crate::leanh::lean_ctor_set(v___x_2665_, 2, v_lctx_2663_);
    crate::leanh::lean_ctor_set(v___x_2665_, 3, v_options_2664_);
    v___x_2666_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2666_, 0, v___x_2665_);
    crate::leanh::lean_ctor_set(v___x_2666_, 1, v_msgData_2653_);
    v___x_2667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2667_, 0, v___x_2666_);
    return v___x_2667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(
    mut v_msgData_2668_: *mut crate::leanh::LeanObject,
    mut v___y_2669_: *mut crate::leanh::LeanObject,
    mut v___y_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2674_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
    crate::leanh::lean_dec(v___y_2672_);
    crate::leanh::lean_dec_ref(v___y_2671_);
    crate::leanh::lean_dec(v___y_2670_);
    crate::leanh::lean_dec_ref(v___y_2669_);
    return v_res_2674_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(
    mut v_ref_2676_: *mut crate::leanh::LeanObject,
    mut v_msgData_2677_: *mut crate::leanh::LeanObject,
    mut v_severity_2678_: u8,
    mut v_isSilent_2679_: u8,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
    mut v___y_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: u8 = 0;
    let mut v___y_2690_: u8 = 0;
    let mut v___y_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v___y_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: u8 = 0;
    let mut v___y_2727_: u8 = 0;
    let mut v___y_2728_: u8 = 0;
    let mut v___y_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v___y_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: u8 = 0;
    let mut v___y_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: u8 = 0;
    let mut v___y_2753_: u8 = 0;
    let mut v___y_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: u8 = 0;
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: u8 = 0;
    let mut v_ref_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___y_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: u8 = 0;
    let mut v___y_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: u8 = 0;
    let mut v___y_2777_: u8 = 0;
    let mut v___y_2779_: u8 = 0;
    let mut v_fileName_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2784_: u8 = 0;
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2769_ = 2;
                v___x_2794_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2678_, v___x_2769_);
                if v___x_2794_ == 0 {
                    v___y_2779_ = v___x_2794_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2677_);
                    v___x_2795_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2677_);
                    v___y_2779_ = v___x_2795_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2695_ = lean_st_ref_take(v___y_2694_);
                v_currNamespace_2696_ = crate::leanh::lean_ctor_get(v___y_2693_, 6);
                v_openDecls_2697_ = crate::leanh::lean_ctor_get(v___y_2693_, 7);
                v_env_2698_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                v_nextMacroScope_2699_ = crate::leanh::lean_ctor_get(v___x_2695_, 1);
                v_ngen_2700_ = crate::leanh::lean_ctor_get(v___x_2695_, 2);
                v_auxDeclNGen_2701_ = crate::leanh::lean_ctor_get(v___x_2695_, 3);
                v_traceState_2702_ = crate::leanh::lean_ctor_get(v___x_2695_, 4);
                v_cache_2703_ = crate::leanh::lean_ctor_get(v___x_2695_, 5);
                v_messages_2704_ = crate::leanh::lean_ctor_get(v___x_2695_, 6);
                v_infoState_2705_ = crate::leanh::lean_ctor_get(v___x_2695_, 7);
                v_snapshotTasks_2706_ = crate::leanh::lean_ctor_get(v___x_2695_, 8);
                v_isSharedCheck_2720_ = (!crate::leanh::lean_is_exclusive(v___x_2695_)) as u8;
                if v_isSharedCheck_2720_ == 0 {
                    v___x_2708_ = v___x_2695_;
                    v_isShared_2709_ = v_isSharedCheck_2720_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2706_);
                    crate::leanh::lean_inc(v_infoState_2705_);
                    crate::leanh::lean_inc(v_messages_2704_);
                    crate::leanh::lean_inc(v_cache_2703_);
                    crate::leanh::lean_inc(v_traceState_2702_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2701_);
                    crate::leanh::lean_inc(v_ngen_2700_);
                    crate::leanh::lean_inc(v_nextMacroScope_2699_);
                    crate::leanh::lean_inc(v_env_2698_);
                    crate::leanh::lean_dec(v___x_2695_);
                    v___x_2708_ = crate::leanh::lean_box(0);
                    v_isShared_2709_ = v_isSharedCheck_2720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_2697_);
                crate::leanh::lean_inc(v_currNamespace_2696_);
                v___x_2710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2710_, 0, v_currNamespace_2696_);
                crate::leanh::lean_ctor_set(v___x_2710_, 1, v_openDecls_2697_);
                v___x_2711_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2711_, 0, v___x_2710_);
                crate::leanh::lean_ctor_set(v___x_2711_, 1, v___y_2686_);
                crate::leanh::lean_inc_ref(v___y_2691_);
                crate::leanh::lean_inc_ref(v___y_2688_);
                v___x_2712_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2712_, 0, v___y_2688_);
                crate::leanh::lean_ctor_set(v___x_2712_, 1, v___y_2692_);
                crate::leanh::lean_ctor_set(v___x_2712_, 2, v___y_2687_);
                crate::leanh::lean_ctor_set(v___x_2712_, 3, v___y_2691_);
                crate::leanh::lean_ctor_set(v___x_2712_, 4, v___x_2711_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2690_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2689_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2679_,
                );
                v___x_2713_ = l_Lean_MessageLog_add(v___x_2712_, v_messages_2704_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 6, v___x_2713_);
                    v___x_2715_ = v___x_2708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_env_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_nextMacroScope_2699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_ngen_2700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 3, v_auxDeclNGen_2701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_traceState_2702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 5, v_cache_2703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 6, v___x_2713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 7, v_infoState_2705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 8, v_snapshotTasks_2706_);
                    v___x_2715_ = v_reuseFailAlloc_2719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2716_ = lean_st_ref_set(v___y_2694_, v___x_2715_);
                v___x_2717_ = crate::leanh::lean_box(0);
                v___x_2718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2717_);
                return v___x_2718_;
            }
            4 => {
                v___x_2730_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2677_,
                    );
                v___x_2731_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_2730_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
                v_a_2732_ = crate::leanh::lean_ctor_get(v___x_2731_, 0);
                v_isSharedCheck_2745_ = (!crate::leanh::lean_is_exclusive(v___x_2731_)) as u8;
                if v_isSharedCheck_2745_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    v_isShared_2735_ = v_isSharedCheck_2745_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2732_);
                    crate::leanh::lean_dec(v___x_2731_);
                    v___x_2734_ = crate::leanh::lean_box(0);
                    v_isShared_2735_ = v_isSharedCheck_2745_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_2724_, 2);
                v___x_2736_ = l_Lean_FileMap_toPosition(v___y_2724_, v___y_2723_);
                crate::leanh::lean_dec(v___y_2723_);
                v___x_2737_ = l_Lean_FileMap_toPosition(v___y_2724_, v___y_2729_);
                crate::leanh::lean_dec(v___y_2729_);
                v___x_2738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2738_, 0, v___x_2737_);
                v___x_2739_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0;
                if v___y_2728_ == 0 {
                    crate::leanh::lean_del_object(v___x_2734_);
                    crate::leanh::lean_dec_ref(v___y_2722_);
                    v___y_2686_ = v_a_2732_;
                    v___y_2687_ = v___x_2738_;
                    v___y_2688_ = v___y_2725_;
                    v___y_2689_ = v___y_2726_;
                    v___y_2690_ = v___y_2727_;
                    v___y_2691_ = v___x_2739_;
                    v___y_2692_ = v___x_2736_;
                    v___y_2693_ = v___y_2682_;
                    v___y_2694_ = v___y_2683_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2732_);
                    v___x_2740_ = l_Lean_MessageData_hasTag(v___y_2722_, v_a_2732_);
                    if v___x_2740_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2738_, 1);
                        crate::leanh::lean_dec_ref(v___x_2736_);
                        crate::leanh::lean_dec(v_a_2732_);
                        v___x_2741_ = crate::leanh::lean_box(0);
                        if v_isShared_2735_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2741_);
                            v___x_2743_ = v___x_2734_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2744_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
                            v___x_2743_ = v_reuseFailAlloc_2744_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2734_);
                        v___y_2686_ = v_a_2732_;
                        v___y_2687_ = v___x_2738_;
                        v___y_2688_ = v___y_2725_;
                        v___y_2689_ = v___y_2726_;
                        v___y_2690_ = v___y_2727_;
                        v___y_2691_ = v___x_2739_;
                        v___y_2692_ = v___x_2736_;
                        v___y_2693_ = v___y_2682_;
                        v___y_2694_ = v___y_2683_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2743_;
            }
            7 => {
                v___x_2755_ = l_Lean_Syntax_getTailPos_x3f(v___y_2751_, v___y_2752_);
                crate::leanh::lean_dec(v___y_2751_);
                if crate::leanh::lean_obj_tag(v___x_2755_) == 0 {
                    crate::leanh::lean_inc(v___y_2754_);
                    v___y_2722_ = v___y_2747_;
                    v___y_2723_ = v___y_2754_;
                    v___y_2724_ = v___y_2748_;
                    v___y_2725_ = v___y_2749_;
                    v___y_2726_ = v___y_2750_;
                    v___y_2727_ = v___y_2752_;
                    v___y_2728_ = v___y_2753_;
                    v___y_2729_ = v___y_2754_;
                    state = 4;
                    continue;
                } else {
                    v_val_2756_ = crate::leanh::lean_ctor_get(v___x_2755_, 0);
                    crate::leanh::lean_inc(v_val_2756_);
                    crate::leanh::lean_dec_ref_known(v___x_2755_, 1);
                    v___y_2722_ = v___y_2747_;
                    v___y_2723_ = v___y_2754_;
                    v___y_2724_ = v___y_2748_;
                    v___y_2725_ = v___y_2749_;
                    v___y_2726_ = v___y_2750_;
                    v___y_2727_ = v___y_2752_;
                    v___y_2728_ = v___y_2753_;
                    v___y_2729_ = v_val_2756_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2765_ = l_Lean_replaceRef(v_ref_2676_, v___y_2759_);
                v___x_2766_ = l_Lean_Syntax_getPos_x3f(v_ref_2765_, v___y_2762_);
                if crate::leanh::lean_obj_tag(v___x_2766_) == 0 {
                    v___x_2767_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2747_ = v___y_2758_;
                    v___y_2748_ = v___y_2760_;
                    v___y_2749_ = v___y_2761_;
                    v___y_2750_ = v___y_2764_;
                    v___y_2751_ = v_ref_2765_;
                    v___y_2752_ = v___y_2762_;
                    v___y_2753_ = v___y_2763_;
                    v___y_2754_ = v___x_2767_;
                    state = 7;
                    continue;
                } else {
                    v_val_2768_ = crate::leanh::lean_ctor_get(v___x_2766_, 0);
                    crate::leanh::lean_inc(v_val_2768_);
                    crate::leanh::lean_dec_ref_known(v___x_2766_, 1);
                    v___y_2747_ = v___y_2758_;
                    v___y_2748_ = v___y_2760_;
                    v___y_2749_ = v___y_2761_;
                    v___y_2750_ = v___y_2764_;
                    v___y_2751_ = v_ref_2765_;
                    v___y_2752_ = v___y_2762_;
                    v___y_2753_ = v___y_2763_;
                    v___y_2754_ = v_val_2768_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2777_ == 0 {
                    v___y_2758_ = v___y_2775_;
                    v___y_2759_ = v___y_2771_;
                    v___y_2760_ = v___y_2772_;
                    v___y_2761_ = v___y_2773_;
                    v___y_2762_ = v___y_2776_;
                    v___y_2763_ = v___y_2774_;
                    v___y_2764_ = v_severity_2678_;
                    state = 8;
                    continue;
                } else {
                    v___y_2758_ = v___y_2775_;
                    v___y_2759_ = v___y_2771_;
                    v___y_2760_ = v___y_2772_;
                    v___y_2761_ = v___y_2773_;
                    v___y_2762_ = v___y_2776_;
                    v___y_2763_ = v___y_2774_;
                    v___y_2764_ = v___x_2769_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2779_ == 0 {
                    v_fileName_2780_ = crate::leanh::lean_ctor_get(v___y_2682_, 0);
                    v_fileMap_2781_ = crate::leanh::lean_ctor_get(v___y_2682_, 1);
                    v_options_2782_ = crate::leanh::lean_ctor_get(v___y_2682_, 2);
                    v_ref_2783_ = crate::leanh::lean_ctor_get(v___y_2682_, 5);
                    v_suppressElabErrors_2784_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2682_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2785_ = crate::leanh::lean_box((v___y_2779_) as usize);
                    v___x_2786_ = crate::leanh::lean_box((v_suppressElabErrors_2784_) as usize);
                    v___f_2787_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2787_, 0, v___x_2785_);
                    crate::leanh::lean_closure_set(v___f_2787_, 1, v___x_2786_);
                    v___x_2788_ = 1;
                    v___x_2789_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2678_, v___x_2788_);
                    if v___x_2789_ == 0 {
                        v___y_2771_ = v_ref_2783_;
                        v___y_2772_ = v_fileMap_2781_;
                        v___y_2773_ = v_fileName_2780_;
                        v___y_2774_ = v_suppressElabErrors_2784_;
                        v___y_2775_ = v___f_2787_;
                        v___y_2776_ = v___y_2779_;
                        v___y_2777_ = v___x_2789_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2790_ = l_Lean_warningAsError;
                        v___x_2791_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_options_2782_, v___x_2790_);
                        v___y_2771_ = v_ref_2783_;
                        v___y_2772_ = v_fileMap_2781_;
                        v___y_2773_ = v_fileName_2780_;
                        v___y_2774_ = v_suppressElabErrors_2784_;
                        v___y_2775_ = v___f_2787_;
                        v___y_2776_ = v___y_2779_;
                        v___y_2777_ = v___x_2791_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2677_);
                    v___x_2792_ = crate::leanh::lean_box(0);
                    v___x_2793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2793_, 0, v___x_2792_);
                    return v___x_2793_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(
    mut v_ref_2796_: *mut crate::leanh::LeanObject,
    mut v_msgData_2797_: *mut crate::leanh::LeanObject,
    mut v_severity_2798_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
    mut v___y_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
    mut v___y_2803_: *mut crate::leanh::LeanObject,
    mut v___y_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2805_: u8 = 0;
    let mut v_isSilent_boxed_2806_: u8 = 0;
    let mut v_res_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2805_ = (crate::leanh::lean_unbox(v_severity_2798_) as u8);
    v_isSilent_boxed_2806_ = (crate::leanh::lean_unbox(v_isSilent_2799_) as u8);
    v_res_2807_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_2796_, v_msgData_2797_, v_severity_boxed_2805_, v_isSilent_boxed_2806_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
    crate::leanh::lean_dec(v___y_2803_);
    crate::leanh::lean_dec_ref(v___y_2802_);
    crate::leanh::lean_dec(v___y_2801_);
    crate::leanh::lean_dec_ref(v___y_2800_);
    crate::leanh::lean_dec(v_ref_2796_);
    return v_res_2807_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(
    mut v_msgData_2808_: *mut crate::leanh::LeanObject,
    mut v_severity_2809_: u8,
    mut v_isSilent_2810_: u8,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
    mut v___y_2813_: *mut crate::leanh::LeanObject,
    mut v___y_2814_: *mut crate::leanh::LeanObject,
    mut v___y_2815_: *mut crate::leanh::LeanObject,
    mut v___y_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2818_ = crate::leanh::lean_ctor_get(v___y_2815_, 5);
    v___x_2819_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_2818_, v_msgData_2808_, v_severity_2809_, v_isSilent_2810_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
    return v___x_2819_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(
    mut v_msgData_2820_: *mut crate::leanh::LeanObject,
    mut v_severity_2821_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2830_: u8 = 0;
    let mut v_isSilent_boxed_2831_: u8 = 0;
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2830_ = (crate::leanh::lean_unbox(v_severity_2821_) as u8);
    v_isSilent_boxed_2831_ = (crate::leanh::lean_unbox(v_isSilent_2822_) as u8);
    v_res_2832_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_2820_, v_severity_boxed_2830_, v_isSilent_boxed_2831_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
    crate::leanh::lean_dec(v___y_2828_);
    crate::leanh::lean_dec_ref(v___y_2827_);
    crate::leanh::lean_dec(v___y_2826_);
    crate::leanh::lean_dec_ref(v___y_2825_);
    crate::leanh::lean_dec(v___y_2824_);
    crate::leanh::lean_dec_ref(v___y_2823_);
    return v_res_2832_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(
    mut v_msgData_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = 2;
    v___x_2842_ = 0;
    v___x_2843_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_2833_, v___x_2841_, v___x_2842_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
    return v___x_2843_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(
    mut v_msgData_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
    mut v___y_2847_: *mut crate::leanh::LeanObject,
    mut v___y_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(
        v_msgData_2844_,
        v___y_2845_,
        v___y_2846_,
        v___y_2847_,
        v___y_2848_,
        v___y_2849_,
        v___y_2850_,
    );
    crate::leanh::lean_dec(v___y_2850_);
    crate::leanh::lean_dec_ref(v___y_2849_);
    crate::leanh::lean_dec(v___y_2848_);
    crate::leanh::lean_dec_ref(v___y_2847_);
    crate::leanh::lean_dec(v___y_2846_);
    crate::leanh::lean_dec_ref(v___y_2845_);
    return v_res_2852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(
    mut v_as_2856_: *mut crate::leanh::LeanObject,
    mut v_sz_2857_: usize,
    mut v_i_2858_: usize,
    mut v_b_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2865_ = lean_usize_dec_lt(v_i_2858_, v_sz_2857_);
                if v___x_2865_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_2859_);
                    return v_b_2859_;
                } else {
                    v___x_2866_ = crate::leanh::lean_box(0);
                    v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0;
                    v_a_2868_ = lean_array_uget_borrowed(v_as_2856_, v_i_2858_);
                    v___x_2869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2;
                    crate::leanh::lean_inc(v_a_2868_);
                    v___x_2870_ = l_Lean_Syntax_isOfKind(v_a_2868_, v___x_2869_);
                    if v___x_2870_ == 0 {
                        v_a_2861_ = v___x_2867_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2871_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2872_ = l_Lean_Syntax_getArg(v_a_2868_, v___x_2871_);
                        v___x_2873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4;
                        crate::leanh::lean_inc(v___x_2872_);
                        v___x_2874_ = l_Lean_Syntax_isOfKind(v___x_2872_, v___x_2873_);
                        if v___x_2874_ == 0 {
                            crate::leanh::lean_dec(v___x_2872_);
                            v_a_2861_ = v___x_2867_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2875_ = l_Lean_TSyntax_getId(v___x_2872_);
                            crate::leanh::lean_dec(v___x_2872_);
                            v___x_2876_ = l_Lean_extractMacroScopes(v___x_2875_);
                            v___x_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2877_, 0, v___x_2876_);
                            v___x_2878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2878_, 0, v___x_2877_);
                            v___x_2879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2878_);
                            crate::leanh::lean_ctor_set(v___x_2879_, 1, v___x_2866_);
                            return v___x_2879_;
                        }
                    }
                }
            }
            1 => {
                v___x_2862_ = 1usize;
                v___x_2863_ = lean_usize_add(v_i_2858_, v___x_2862_);
                v_i_2858_ = v___x_2863_;
                v_b_2859_ = v_a_2861_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___boxed(
    mut v_as_2880_: *mut crate::leanh::LeanObject,
    mut v_sz_2881_: *mut crate::leanh::LeanObject,
    mut v_i_2882_: *mut crate::leanh::LeanObject,
    mut v_b_2883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2884_: usize = 0;
    let mut v_i_boxed_2885_: usize = 0;
    let mut v_res_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2884_ = crate::leanh::lean_unbox_usize(v_sz_2881_);
    crate::leanh::lean_dec(v_sz_2881_);
    v_i_boxed_2885_ = crate::leanh::lean_unbox_usize(v_i_2882_);
    crate::leanh::lean_dec(v_i_2882_);
    v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_2880_, v_sz_boxed_2884_, v_i_boxed_2885_, v_b_2883_);
    crate::leanh::lean_dec_ref(v_b_2883_);
    crate::leanh::lean_dec_ref(v_as_2880_);
    return v_res_2886_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(
    mut v_x_2887_: *mut crate::leanh::LeanObject,
    mut v_x_2888_: *mut crate::leanh::LeanObject,
    mut v_x_2889_: *mut crate::leanh::LeanObject,
    mut v_x_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2895_: u8 = 0;
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2891_ = crate::leanh::lean_ctor_get(v_x_2887_, 0);
                v_vs_2892_ = crate::leanh::lean_ctor_get(v_x_2887_, 1);
                v_isSharedCheck_2916_ = (!crate::leanh::lean_is_exclusive(v_x_2887_)) as u8;
                if v_isSharedCheck_2916_ == 0 {
                    v___x_2894_ = v_x_2887_;
                    v_isShared_2895_ = v_isSharedCheck_2916_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2892_);
                    crate::leanh::lean_inc(v_ks_2891_);
                    crate::leanh::lean_dec(v_x_2887_);
                    v___x_2894_ = crate::leanh::lean_box(0);
                    v_isShared_2895_ = v_isSharedCheck_2916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2896_ = lean_array_get_size(v_ks_2891_);
                v___x_2897_ = lean_nat_dec_lt(v_x_2888_, v___x_2896_);
                if v___x_2897_ == 0 {
                    crate::leanh::lean_dec(v_x_2888_);
                    v___x_2898_ = lean_array_push(v_ks_2891_, v_x_2889_);
                    v___x_2899_ = lean_array_push(v_vs_2892_, v_x_2890_);
                    if v_isShared_2895_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2894_, 1, v___x_2899_);
                        crate::leanh::lean_ctor_set(v___x_2894_, 0, v___x_2898_);
                        v___x_2901_ = v___x_2894_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2899_);
                        v___x_2901_ = v_reuseFailAlloc_2902_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2903_ = lean_array_fget_borrowed(v_ks_2891_, v_x_2888_);
                    v___x_2904_ = l_Lean_instBEqMVarId_beq(v_x_2889_, v_k_x27_2903_);
                    if v___x_2904_ == 0 {
                        if v_isShared_2895_ == 0 {
                            v___x_2906_ = v___x_2894_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2910_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_ks_2891_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_vs_2892_);
                            v___x_2906_ = v_reuseFailAlloc_2910_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2911_ = lean_array_fset(v_ks_2891_, v_x_2888_, v_x_2889_);
                        v___x_2912_ = lean_array_fset(v_vs_2892_, v_x_2888_, v_x_2890_);
                        crate::leanh::lean_dec(v_x_2888_);
                        if v_isShared_2895_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2894_, 1, v___x_2912_);
                            crate::leanh::lean_ctor_set(v___x_2894_, 0, v___x_2911_);
                            v___x_2914_ = v___x_2894_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2915_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2911_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2912_);
                            v___x_2914_ = v_reuseFailAlloc_2915_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2901_;
            }
            3 => {
                v___x_2907_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2908_ = lean_nat_add(v_x_2888_, v___x_2907_);
                crate::leanh::lean_dec(v_x_2888_);
                v_x_2887_ = v___x_2906_;
                v_x_2888_ = v___x_2908_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(
    mut v_n_2917_: *mut crate::leanh::LeanObject,
    mut v_k_2918_: *mut crate::leanh::LeanObject,
    mut v_v_2919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2920_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_n_2917_, v___x_2920_, v_k_2918_, v_v_2919_);
    return v___x_2921_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: usize = 0;
    let mut v___x_2924_: usize = 0;
    v___x_2922_ = 5usize;
    v___x_2923_ = 1usize;
    v___x_2924_ = lean_usize_shift_left(v___x_2923_, v___x_2922_);
    return v___x_2924_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1()
-> usize {
    let mut v___x_2925_: usize = 0;
    let mut v___x_2926_: usize = 0;
    let mut v___x_2927_: usize = 0;
    v___x_2925_ = 1usize;
    v___x_2926_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
    v___x_2927_ = lean_usize_sub(v___x_2926_, v___x_2925_);
    return v___x_2927_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2928_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2928_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(
    mut v_x_2929_: *mut crate::leanh::LeanObject,
    mut v_x_2930_: usize,
    mut v_x_2931_: usize,
    mut v_x_2932_: *mut crate::leanh::LeanObject,
    mut v_x_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: usize = 0;
    let mut v___x_2936_: usize = 0;
    let mut v___x_2937_: usize = 0;
    let mut v___x_2938_: usize = 0;
    let mut v_j_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v_v_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_node_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: usize = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_unused_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: u8 = 0;
    let mut v_ks_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: usize = 0;
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u8 = 0;
    let mut v_reuseFailAlloc_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2929_) == 0 {
                    v_es_2934_ = crate::leanh::lean_ctor_get(v_x_2929_, 0);
                    v___x_2935_ = 5usize;
                    v___x_2936_ = 1usize;
                    v___x_2937_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1);
                    v___x_2938_ = lean_usize_land(v_x_2930_, v___x_2937_);
                    v_j_2939_ = lean_usize_to_nat(v___x_2938_);
                    v___x_2940_ = lean_array_get_size(v_es_2934_);
                    v___x_2941_ = lean_nat_dec_lt(v_j_2939_, v___x_2940_);
                    if v___x_2941_ == 0 {
                        crate::leanh::lean_dec(v_j_2939_);
                        crate::leanh::lean_dec(v_x_2933_);
                        crate::leanh::lean_dec(v_x_2932_);
                        return v_x_2929_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2934_);
                        v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v_x_2929_)) as u8;
                        if v_isSharedCheck_2978_ == 0 {
                            v_unused_2979_ = crate::leanh::lean_ctor_get(v_x_2929_, 0);
                            crate::leanh::lean_dec(v_unused_2979_);
                            v___x_2943_ = v_x_2929_;
                            v_isShared_2944_ = v_isSharedCheck_2978_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2929_);
                            v___x_2943_ = crate::leanh::lean_box(0);
                            v_isShared_2944_ = v_isSharedCheck_2978_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2980_ = crate::leanh::lean_ctor_get(v_x_2929_, 0);
                    v_vs_2981_ = crate::leanh::lean_ctor_get(v_x_2929_, 1);
                    v_isSharedCheck_3001_ = (!crate::leanh::lean_is_exclusive(v_x_2929_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2983_ = v_x_2929_;
                        v_isShared_2984_ = v_isSharedCheck_3001_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2981_);
                        crate::leanh::lean_inc(v_ks_2980_);
                        crate::leanh::lean_dec(v_x_2929_);
                        v___x_2983_ = crate::leanh::lean_box(0);
                        v_isShared_2984_ = v_isSharedCheck_3001_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2945_ = lean_array_fget(v_es_2934_, v_j_2939_);
                v___x_2946_ = crate::leanh::lean_box(0);
                v_xs_x27_2947_ = lean_array_fset(v_es_2934_, v_j_2939_, v___x_2946_);
                match crate::leanh::lean_obj_tag(v_v_2945_) {
                    0 => {
                        v_key_2954_ = crate::leanh::lean_ctor_get(v_v_2945_, 0);
                        v_val_2955_ = crate::leanh::lean_ctor_get(v_v_2945_, 1);
                        v_isSharedCheck_2965_ = (!crate::leanh::lean_is_exclusive(v_v_2945_)) as u8;
                        if v_isSharedCheck_2965_ == 0 {
                            v___x_2957_ = v_v_2945_;
                            v_isShared_2958_ = v_isSharedCheck_2965_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2955_);
                            crate::leanh::lean_inc(v_key_2954_);
                            crate::leanh::lean_dec(v_v_2945_);
                            v___x_2957_ = crate::leanh::lean_box(0);
                            v_isShared_2958_ = v_isSharedCheck_2965_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2966_ = crate::leanh::lean_ctor_get(v_v_2945_, 0);
                        v_isSharedCheck_2976_ = (!crate::leanh::lean_is_exclusive(v_v_2945_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2968_ = v_v_2945_;
                            v_isShared_2969_ = v_isSharedCheck_2976_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2966_);
                            crate::leanh::lean_dec(v_v_2945_);
                            v___x_2968_ = crate::leanh::lean_box(0);
                            v_isShared_2969_ = v_isSharedCheck_2976_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2977_, 0, v_x_2932_);
                        crate::leanh::lean_ctor_set(v___x_2977_, 1, v_x_2933_);
                        v___y_2949_ = v___x_2977_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2950_ = lean_array_fset(v_xs_x27_2947_, v_j_2939_, v___y_2949_);
                crate::leanh::lean_dec(v_j_2939_);
                if v_isShared_2944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2943_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2952_;
            }
            4 => {
                v___x_2959_ = l_Lean_instBEqMVarId_beq(v_x_2932_, v_key_2954_);
                if v___x_2959_ == 0 {
                    crate::leanh::lean_del_object(v___x_2957_);
                    v___x_2960_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2954_,
                        v_val_2955_,
                        v_x_2932_,
                        v_x_2933_,
                    );
                    v___x_2961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2961_, 0, v___x_2960_);
                    v___y_2949_ = v___x_2961_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2955_);
                    crate::leanh::lean_dec(v_key_2954_);
                    if v_isShared_2958_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2957_, 1, v_x_2933_);
                        crate::leanh::lean_ctor_set(v___x_2957_, 0, v_x_2932_);
                        v___x_2963_ = v___x_2957_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_x_2932_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_x_2933_);
                        v___x_2963_ = v_reuseFailAlloc_2964_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2949_ = v___x_2963_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2970_ = lean_usize_shift_right(v_x_2930_, v___x_2935_);
                v___x_2971_ = lean_usize_add(v_x_2931_, v___x_2936_);
                v___x_2972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_node_2966_, v___x_2970_, v___x_2971_, v_x_2932_, v_x_2933_);
                if v_isShared_2969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2968_, 0, v___x_2972_);
                    v___x_2974_ = v___x_2968_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2949_ = v___x_2974_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2984_ == 0 {
                    v___x_2986_ = v___x_2983_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3000_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_ks_2980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_vs_2981_);
                    v___x_2986_ = v_reuseFailAlloc_3000_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2987_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v___x_2986_, v_x_2932_, v_x_2933_);
                v___x_2995_ = 7usize;
                v___x_2996_ = lean_usize_dec_le(v___x_2995_, v_x_2931_);
                if v___x_2996_ == 0 {
                    v___x_2997_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2987_);
                    v___x_2998_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2999_ = lean_nat_dec_lt(v___x_2997_, v___x_2998_);
                    crate::leanh::lean_dec(v___x_2997_);
                    v___y_2989_ = v___x_2999_;
                    state = 10;
                    continue;
                } else {
                    v___y_2989_ = v___x_2996_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2989_ == 0 {
                    v_ks_2990_ = crate::leanh::lean_ctor_get(v_newNode_2987_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2990_);
                    v_vs_2991_ = crate::leanh::lean_ctor_get(v_newNode_2987_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2991_);
                    crate::leanh::lean_dec_ref(v_newNode_2987_);
                    v___x_2992_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2);
                    v___x_2994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_2931_, v_ks_2990_, v_vs_2991_, v___x_2992_, v___x_2993_);
                    crate::leanh::lean_dec_ref(v_vs_2991_);
                    crate::leanh::lean_dec_ref(v_ks_2990_);
                    return v___x_2994_;
                } else {
                    return v_newNode_2987_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(
    mut v_depth_3002_: usize,
    mut v_keys_3003_: *mut crate::leanh::LeanObject,
    mut v_vals_3004_: *mut crate::leanh::LeanObject,
    mut v_i_3005_: *mut crate::leanh::LeanObject,
    mut v_entries_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v_k_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: u64 = 0;
    let mut v_h_3012_: usize = 0;
    let mut v___x_3013_: usize = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: usize = 0;
    let mut v___x_3017_: usize = 0;
    let mut v_h_3018_: usize = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = lean_array_get_size(v_keys_3003_);
                v___x_3008_ = lean_nat_dec_lt(v_i_3005_, v___x_3007_);
                if v___x_3008_ == 0 {
                    crate::leanh::lean_dec(v_i_3005_);
                    return v_entries_3006_;
                } else {
                    v_k_3009_ = lean_array_fget_borrowed(v_keys_3003_, v_i_3005_);
                    v_v_3010_ = lean_array_fget_borrowed(v_vals_3004_, v_i_3005_);
                    v___x_3011_ = l_Lean_instHashableMVarId_hash(v_k_3009_);
                    v_h_3012_ = lean_uint64_to_usize(v___x_3011_);
                    v___x_3013_ = 5usize;
                    v___x_3014_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3015_ = 1usize;
                    v___x_3016_ = lean_usize_sub(v_depth_3002_, v___x_3015_);
                    v___x_3017_ = lean_usize_mul(v___x_3013_, v___x_3016_);
                    v_h_3018_ = lean_usize_shift_right(v_h_3012_, v___x_3017_);
                    v___x_3019_ = lean_nat_add(v_i_3005_, v___x_3014_);
                    crate::leanh::lean_dec(v_i_3005_);
                    crate::leanh::lean_inc(v_v_3010_);
                    crate::leanh::lean_inc(v_k_3009_);
                    v___x_3020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_entries_3006_, v_h_3018_, v_depth_3002_, v_k_3009_, v_v_3010_);
                    v_i_3005_ = v___x_3019_;
                    v_entries_3006_ = v___x_3020_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg___boxed(
    mut v_depth_3022_: *mut crate::leanh::LeanObject,
    mut v_keys_3023_: *mut crate::leanh::LeanObject,
    mut v_vals_3024_: *mut crate::leanh::LeanObject,
    mut v_i_3025_: *mut crate::leanh::LeanObject,
    mut v_entries_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3027_: usize = 0;
    let mut v_res_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3027_ = crate::leanh::lean_unbox_usize(v_depth_3022_);
    crate::leanh::lean_dec(v_depth_3022_);
    v_res_3028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_3027_, v_keys_3023_, v_vals_3024_, v_i_3025_, v_entries_3026_);
    crate::leanh::lean_dec_ref(v_vals_3024_);
    crate::leanh::lean_dec_ref(v_keys_3023_);
    return v_res_3028_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_x_3029_: *mut crate::leanh::LeanObject,
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v_x_3031_: *mut crate::leanh::LeanObject,
    mut v_x_3032_: *mut crate::leanh::LeanObject,
    mut v_x_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_24196__boxed_3034_: usize = 0;
    let mut v_x_24197__boxed_3035_: usize = 0;
    let mut v_res_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_24196__boxed_3034_ = crate::leanh::lean_unbox_usize(v_x_3030_);
    crate::leanh::lean_dec(v_x_3030_);
    v_x_24197__boxed_3035_ = crate::leanh::lean_unbox_usize(v_x_3031_);
    crate::leanh::lean_dec(v_x_3031_);
    v_res_3036_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3029_, v_x_24196__boxed_3034_, v_x_24197__boxed_3035_, v_x_3032_, v_x_3033_);
    return v_res_3036_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(
    mut v_x_3037_: *mut crate::leanh::LeanObject,
    mut v_x_3038_: *mut crate::leanh::LeanObject,
    mut v_x_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: u64 = 0;
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = l_Lean_instHashableMVarId_hash(v_x_3038_);
    v___x_3041_ = lean_uint64_to_usize(v___x_3040_);
    v___x_3042_ = 1usize;
    v___x_3043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3037_, v___x_3041_, v___x_3042_, v_x_3038_, v_x_3039_);
    return v___x_3043_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
    mut v_mvarId_3044_: *mut crate::leanh::LeanObject,
    mut v_val_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v_depth_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_isSharedCheck_3081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3048_ = lean_st_ref_take(v___y_3046_);
                v_mctx_3049_ = crate::leanh::lean_ctor_get(v___x_3048_, 0);
                v_cache_3050_ = crate::leanh::lean_ctor_get(v___x_3048_, 1);
                v_zetaDeltaFVarIds_3051_ = crate::leanh::lean_ctor_get(v___x_3048_, 2);
                v_postponed_3052_ = crate::leanh::lean_ctor_get(v___x_3048_, 3);
                v_diag_3053_ = crate::leanh::lean_ctor_get(v___x_3048_, 4);
                v_isSharedCheck_3081_ = (!crate::leanh::lean_is_exclusive(v___x_3048_)) as u8;
                if v_isSharedCheck_3081_ == 0 {
                    v___x_3055_ = v___x_3048_;
                    v_isShared_3056_ = v_isSharedCheck_3081_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3053_);
                    crate::leanh::lean_inc(v_postponed_3052_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3051_);
                    crate::leanh::lean_inc(v_cache_3050_);
                    crate::leanh::lean_inc(v_mctx_3049_);
                    crate::leanh::lean_dec(v___x_3048_);
                    v___x_3055_ = crate::leanh::lean_box(0);
                    v_isShared_3056_ = v_isSharedCheck_3081_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3057_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 0);
                v_levelAssignDepth_3058_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 1);
                v_lmvarCounter_3059_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 2);
                v_mvarCounter_3060_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 3);
                v_lDecls_3061_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 4);
                v_decls_3062_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 5);
                v_userNames_3063_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 6);
                v_lAssignment_3064_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 7);
                v_eAssignment_3065_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 8);
                v_dAssignment_3066_ = crate::leanh::lean_ctor_get(v_mctx_3049_, 9);
                v_isSharedCheck_3080_ = (!crate::leanh::lean_is_exclusive(v_mctx_3049_)) as u8;
                if v_isSharedCheck_3080_ == 0 {
                    v___x_3068_ = v_mctx_3049_;
                    v_isShared_3069_ = v_isSharedCheck_3080_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3066_);
                    crate::leanh::lean_inc(v_eAssignment_3065_);
                    crate::leanh::lean_inc(v_lAssignment_3064_);
                    crate::leanh::lean_inc(v_userNames_3063_);
                    crate::leanh::lean_inc(v_decls_3062_);
                    crate::leanh::lean_inc(v_lDecls_3061_);
                    crate::leanh::lean_inc(v_mvarCounter_3060_);
                    crate::leanh::lean_inc(v_lmvarCounter_3059_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3058_);
                    crate::leanh::lean_inc(v_depth_3057_);
                    crate::leanh::lean_dec(v_mctx_3049_);
                    v___x_3068_ = crate::leanh::lean_box(0);
                    v_isShared_3069_ = v_isSharedCheck_3080_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3070_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_3065_, v_mvarId_3044_, v_val_3045_);
                if v_isShared_3069_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3068_, 8, v___x_3070_);
                    v___x_3072_ = v___x_3068_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_depth_3057_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3079_,
                        1,
                        v_levelAssignDepth_3058_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_lmvarCounter_3059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_mvarCounter_3060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_lDecls_3061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 5, v_decls_3062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_userNames_3063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_lAssignment_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 8, v___x_3070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 9, v_dAssignment_3066_);
                    v___x_3072_ = v_reuseFailAlloc_3079_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3055_, 0, v___x_3072_);
                    v___x_3074_ = v___x_3055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_cache_3050_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3078_,
                        2,
                        v_zetaDeltaFVarIds_3051_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 3, v_postponed_3052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 4, v_diag_3053_);
                    v___x_3074_ = v_reuseFailAlloc_3078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3075_ = lean_st_ref_set(v___y_3046_, v___x_3074_);
                v___x_3076_ = crate::leanh::lean_box(0);
                v___x_3077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3077_, 0, v___x_3076_);
                return v___x_3077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(
    mut v_mvarId_3082_: *mut crate::leanh::LeanObject,
    mut v_val_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
            v_mvarId_3082_,
            v_val_3083_,
            v___y_3084_,
        );
    crate::leanh::lean_dec(v___y_3084_);
    return v_res_3086_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = l_Lean_NameSet_empty;
    v___x_3090_ = l_Lean_Elab_Tactic_renameInaccessibles___closed__0;
    v___x_3091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3090_);
    crate::leanh::lean_ctor_set(v___x_3091_, 1, v___x_3089_);
    return v___x_3091_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Elab_Tactic_renameInaccessibles___closed__2;
    v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles(
    mut v_mvarId_3097_: *mut crate::leanh::LeanObject,
    mut v_hs_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_a_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3155_: usize = 0;
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_unused_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v_a_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_reuseFailAlloc_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut v_unused_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_a_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3106_ = lean_array_get_size(v_hs_3098_);
                v___x_3107_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
                if v___x_3108_ == 0 {
                    crate::leanh::lean_inc(v_mvarId_3097_);
                    v___x_3109_ = l_Lean_MVarId_getDecl(
                        v_mvarId_3097_,
                        v_a_3101_,
                        v_a_3102_,
                        v_a_3103_,
                        v_a_3104_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3109_) == 0 {
                        v_a_3110_ = crate::leanh::lean_ctor_get(v___x_3109_, 0);
                        v_isSharedCheck_3212_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3109_)) as u8;
                        if v_isSharedCheck_3212_ == 0 {
                            v___x_3112_ = v___x_3109_;
                            v_isShared_3113_ = v_isSharedCheck_3212_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3110_);
                            crate::leanh::lean_dec(v___x_3109_);
                            v___x_3112_ = crate::leanh::lean_box(0);
                            v_isShared_3113_ = v_isSharedCheck_3212_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_hs_3098_);
                        crate::leanh::lean_dec(v_mvarId_3097_);
                        v_a_3213_ = crate::leanh::lean_ctor_get(v___x_3109_, 0);
                        v_isSharedCheck_3220_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3109_)) as u8;
                        if v_isSharedCheck_3220_ == 0 {
                            v___x_3215_ = v___x_3109_;
                            v_isShared_3216_ = v_isSharedCheck_3220_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3213_);
                            crate::leanh::lean_dec(v___x_3109_);
                            v___x_3215_ = crate::leanh::lean_box(0);
                            v_isShared_3216_ = v_isSharedCheck_3220_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_hs_3098_);
                    v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3221_, 0, v_mvarId_3097_);
                    return v___x_3221_;
                }
            }
            1 => {
                v___x_3114_ = crate::leanh::lean_box(0);
                v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0;
                v_sz_3116_ = lean_array_size(v_hs_3098_);
                v___x_3117_ = 0usize;
                v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_3098_, v_sz_3116_, v___x_3117_, v___x_3115_);
                v_fst_3119_ = crate::leanh::lean_ctor_get(v___x_3118_, 0);
                v_isSharedCheck_3210_ = (!crate::leanh::lean_is_exclusive(v___x_3118_)) as u8;
                if v_isSharedCheck_3210_ == 0 {
                    v_unused_3211_ = crate::leanh::lean_ctor_get(v___x_3118_, 1);
                    crate::leanh::lean_dec(v_unused_3211_);
                    v___x_3121_ = v___x_3118_;
                    v_isShared_3122_ = v_isSharedCheck_3210_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3119_);
                    crate::leanh::lean_dec(v___x_3118_);
                    v___x_3121_ = crate::leanh::lean_box(0);
                    v_isShared_3122_ = v_isSharedCheck_3210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_3119_) == 0 {
                    crate::leanh::lean_del_object(v___x_3121_);
                    crate::leanh::lean_dec(v_a_3110_);
                    crate::leanh::lean_dec_ref(v_hs_3098_);
                    if v_isShared_3113_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3112_, 0, v_mvarId_3097_);
                        v___x_3124_ = v___x_3112_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_mvarId_3097_);
                        v___x_3124_ = v_reuseFailAlloc_3125_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_3126_ = crate::leanh::lean_ctor_get(v_fst_3119_, 0);
                    crate::leanh::lean_inc(v_val_3126_);
                    crate::leanh::lean_dec_ref_known(v_fst_3119_, 1);
                    if crate::leanh::lean_obj_tag(v_val_3126_) == 1 {
                        crate::leanh::lean_del_object(v___x_3112_);
                        v_val_3127_ = crate::leanh::lean_ctor_get(v_val_3126_, 0);
                        crate::leanh::lean_inc(v_val_3127_);
                        crate::leanh::lean_dec_ref_known(v_val_3126_, 1);
                        v_userName_3128_ = crate::leanh::lean_ctor_get(v_a_3110_, 0);
                        crate::leanh::lean_inc(v_userName_3128_);
                        v_lctx_3129_ = crate::leanh::lean_ctor_get(v_a_3110_, 1);
                        crate::leanh::lean_inc_ref_n(v_lctx_3129_, 2);
                        v_type_3130_ = crate::leanh::lean_ctor_get(v_a_3110_, 2);
                        crate::leanh::lean_inc_ref(v_type_3130_);
                        v_localInstances_3131_ = crate::leanh::lean_ctor_get(v_a_3110_, 4);
                        crate::leanh::lean_inc_ref(v_localInstances_3131_);
                        crate::leanh::lean_dec(v_a_3110_);
                        v___x_3132_ = lean_local_ctx_num_indices(v_lctx_3129_);
                        v___x_3133_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1,
                        );
                        if v_isShared_3122_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3121_, 1, v___x_3133_);
                            crate::leanh::lean_ctor_set(v___x_3121_, 0, v_hs_3098_);
                            v___x_3135_ = v___x_3121_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3206_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_hs_3098_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3133_);
                            v___x_3135_ = v_reuseFailAlloc_3206_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3126_);
                        crate::leanh::lean_del_object(v___x_3121_);
                        crate::leanh::lean_dec(v_a_3110_);
                        crate::leanh::lean_dec_ref(v_hs_3098_);
                        if v_isShared_3113_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3112_, 0, v_mvarId_3097_);
                            v___x_3208_ = v___x_3112_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_3209_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_mvarId_3097_);
                            v___x_3208_ = v_reuseFailAlloc_3209_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3124_;
            }
            4 => {
                v___x_3136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3136_, 0, v_lctx_3129_);
                crate::leanh::lean_ctor_set(v___x_3136_, 1, v___x_3135_);
                v___x_3137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_3132_, v___x_3132_, v_val_3127_, v___x_3107_, v___x_3136_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
                crate::leanh::lean_dec(v_val_3127_);
                crate::leanh::lean_dec(v___x_3132_);
                if crate::leanh::lean_obj_tag(v___x_3137_) == 0 {
                    v_a_3138_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    crate::leanh::lean_inc(v_a_3138_);
                    crate::leanh::lean_dec_ref_known(v___x_3137_, 1);
                    v_snd_3139_ = crate::leanh::lean_ctor_get(v_a_3138_, 1);
                    crate::leanh::lean_inc(v_snd_3139_);
                    v_snd_3140_ = crate::leanh::lean_ctor_get(v_snd_3139_, 1);
                    crate::leanh::lean_inc(v_snd_3140_);
                    v_fst_3141_ = crate::leanh::lean_ctor_get(v_a_3138_, 0);
                    crate::leanh::lean_inc(v_fst_3141_);
                    crate::leanh::lean_dec(v_a_3138_);
                    v_fst_3142_ = crate::leanh::lean_ctor_get(v_snd_3139_, 0);
                    crate::leanh::lean_inc(v_fst_3142_);
                    crate::leanh::lean_dec(v_snd_3139_);
                    v_fst_3143_ = crate::leanh::lean_ctor_get(v_snd_3140_, 0);
                    crate::leanh::lean_inc(v_fst_3143_);
                    crate::leanh::lean_dec(v_snd_3140_);
                    v___x_3186_ = lean_array_get_size(v_fst_3142_);
                    crate::leanh::lean_dec(v_fst_3142_);
                    v___x_3187_ = lean_nat_dec_eq(v___x_3186_, v___x_3107_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3,
                        );
                        v___x_3189_ =
                            l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(
                                v___x_3188_,
                                v_a_3099_,
                                v_a_3100_,
                                v_a_3101_,
                                v_a_3102_,
                                v_a_3103_,
                                v_a_3104_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3189_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3189_, 1);
                            v___y_3145_ = v_a_3099_;
                            v___y_3146_ = v_a_3100_;
                            v___y_3147_ = v_a_3101_;
                            v___y_3148_ = v_a_3102_;
                            v___y_3149_ = v_a_3103_;
                            v___y_3150_ = v_a_3104_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_3143_);
                            crate::leanh::lean_dec(v_fst_3141_);
                            crate::leanh::lean_dec_ref(v_localInstances_3131_);
                            crate::leanh::lean_dec_ref(v_type_3130_);
                            crate::leanh::lean_dec(v_userName_3128_);
                            crate::leanh::lean_dec(v_mvarId_3097_);
                            v_a_3190_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                            v_isSharedCheck_3197_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3189_)) as u8;
                            if v_isSharedCheck_3197_ == 0 {
                                v___x_3192_ = v___x_3189_;
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3190_);
                                crate::leanh::lean_dec(v___x_3189_);
                                v___x_3192_ = crate::leanh::lean_box(0);
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v___y_3145_ = v_a_3099_;
                        v___y_3146_ = v_a_3100_;
                        v___y_3147_ = v_a_3101_;
                        v___y_3148_ = v_a_3102_;
                        v___y_3149_ = v_a_3103_;
                        v___y_3150_ = v_a_3104_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_localInstances_3131_);
                    crate::leanh::lean_dec_ref(v_type_3130_);
                    crate::leanh::lean_dec(v_userName_3128_);
                    crate::leanh::lean_dec(v_mvarId_3097_);
                    v_a_3198_ = crate::leanh::lean_ctor_get(v___x_3137_, 0);
                    v_isSharedCheck_3205_ = (!crate::leanh::lean_is_exclusive(v___x_3137_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v___x_3200_ = v___x_3137_;
                        v_isShared_3201_ = v_isSharedCheck_3205_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3198_);
                        crate::leanh::lean_dec(v___x_3137_);
                        v___x_3200_ = crate::leanh::lean_box(0);
                        v_isShared_3201_ = v_isSharedCheck_3205_;
                        state = 14;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3151_ = 2;
                v___x_3152_ = l_Lean_Meta_mkFreshExprMVarAt(
                    v_fst_3141_,
                    v_localInstances_3131_,
                    v_type_3130_,
                    v___x_3151_,
                    v_userName_3128_,
                    v___x_3107_,
                    v___y_3147_,
                    v___y_3148_,
                    v___y_3149_,
                    v___y_3150_,
                );
                if crate::leanh::lean_obj_tag(v___x_3152_) == 0 {
                    v_a_3153_ = crate::leanh::lean_ctor_get(v___x_3152_, 0);
                    crate::leanh::lean_inc(v_a_3153_);
                    crate::leanh::lean_dec_ref_known(v___x_3152_, 1);
                    v___x_3154_ = l_Lean_Expr_mvarId_x21(v_a_3153_);
                    v_sz_3155_ = lean_array_size(v_fst_3143_);
                    v___x_3156_ = crate::leanh::lean_box_usize(v_sz_3155_);
                    v___x_3157_ = l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1;
                    v___f_3158_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_3158_, 0, v_fst_3143_);
                    crate::leanh::lean_closure_set(v___f_3158_, 1, v___x_3156_);
                    crate::leanh::lean_closure_set(v___f_3158_, 2, v___x_3157_);
                    crate::leanh::lean_closure_set(v___f_3158_, 3, v___x_3114_);
                    crate::leanh::lean_inc(v___x_3154_);
                    v___x_3159_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed as *mut core::ffi::c_void, 10, 3);
                    crate::leanh::lean_closure_set(v___x_3159_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3159_, 1, v___x_3154_);
                    crate::leanh::lean_closure_set(v___x_3159_, 2, v___f_3158_);
                    v___x_3160_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_3159_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
                    if crate::leanh::lean_obj_tag(v___x_3160_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3160_, 1);
                        v___x_3161_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_3097_, v_a_3153_, v___y_3148_);
                        v_isSharedCheck_3168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3161_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v_unused_3169_ = crate::leanh::lean_ctor_get(v___x_3161_, 0);
                            crate::leanh::lean_dec(v_unused_3169_);
                            v___x_3163_ = v___x_3161_;
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3161_);
                            v___x_3163_ = crate::leanh::lean_box(0);
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3154_);
                        crate::leanh::lean_dec(v_a_3153_);
                        crate::leanh::lean_dec(v_mvarId_3097_);
                        v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3160_, 0);
                        v_isSharedCheck_3177_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3160_)) as u8;
                        if v_isSharedCheck_3177_ == 0 {
                            v___x_3172_ = v___x_3160_;
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3170_);
                            crate::leanh::lean_dec(v___x_3160_);
                            v___x_3172_ = crate::leanh::lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3143_);
                    crate::leanh::lean_dec(v_mvarId_3097_);
                    v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3152_, 0);
                    v_isSharedCheck_3185_ = (!crate::leanh::lean_is_exclusive(v___x_3152_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3180_ = v___x_3152_;
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3178_);
                        crate::leanh::lean_dec(v___x_3152_);
                        v___x_3180_ = crate::leanh::lean_box(0);
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3164_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3163_, 0, v___x_3154_);
                    v___x_3166_ = v___x_3163_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3154_);
                    v___x_3166_ = v_reuseFailAlloc_3167_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3166_;
            }
            8 => {
                if v_isShared_3173_ == 0 {
                    v___x_3175_ = v___x_3172_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
                    v___x_3175_ = v_reuseFailAlloc_3176_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3175_;
            }
            10 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3183_;
            }
            12 => {
                if v_isShared_3193_ == 0 {
                    v___x_3195_ = v___x_3192_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3195_;
            }
            14 => {
                if v_isShared_3201_ == 0 {
                    v___x_3203_ = v___x_3200_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
                    v___x_3203_ = v_reuseFailAlloc_3204_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3203_;
            }
            16 => {
                return v___x_3208_;
            }
            17 => {
                if v_isShared_3216_ == 0 {
                    v___x_3218_ = v___x_3215_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
                    v___x_3218_ = v_reuseFailAlloc_3219_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles___boxed(
    mut v_mvarId_3222_: *mut crate::leanh::LeanObject,
    mut v_hs_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
    mut v_a_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3231_ = l_Lean_Elab_Tactic_renameInaccessibles(
        v_mvarId_3222_,
        v_hs_3223_,
        v_a_3224_,
        v_a_3225_,
        v_a_3226_,
        v_a_3227_,
        v_a_3228_,
        v_a_3229_,
    );
    crate::leanh::lean_dec(v_a_3229_);
    crate::leanh::lean_dec_ref(v_a_3228_);
    crate::leanh::lean_dec(v_a_3227_);
    crate::leanh::lean_dec_ref(v_a_3226_);
    crate::leanh::lean_dec(v_a_3225_);
    crate::leanh::lean_dec_ref(v_a_3224_);
    return v_res_3231_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(
    mut v_00_u03b1_3232_: *mut crate::leanh::LeanObject,
    mut v_x_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
    return v___x_3241_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(
    mut v_00_u03b1_3242_: *mut crate::leanh::LeanObject,
    mut v_x_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(
            v_00_u03b1_3242_,
            v_x_3243_,
            v___y_3244_,
            v___y_3245_,
            v___y_3246_,
            v___y_3247_,
            v___y_3248_,
            v___y_3249_,
        );
    crate::leanh::lean_dec(v___y_3249_);
    crate::leanh::lean_dec_ref(v___y_3248_);
    crate::leanh::lean_dec(v___y_3247_);
    crate::leanh::lean_dec_ref(v___y_3246_);
    crate::leanh::lean_dec(v___y_3245_);
    crate::leanh::lean_dec_ref(v___y_3244_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(
    mut v_mvarId_3252_: *mut crate::leanh::LeanObject,
    mut v_val_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3261_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
            v_mvarId_3252_,
            v_val_3253_,
            v___y_3257_,
        );
    return v___x_3261_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(
    mut v_mvarId_3262_: *mut crate::leanh::LeanObject,
    mut v_val_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3271_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(
        v_mvarId_3262_,
        v_val_3263_,
        v___y_3264_,
        v___y_3265_,
        v___y_3266_,
        v___y_3267_,
        v___y_3268_,
        v___y_3269_,
    );
    crate::leanh::lean_dec(v___y_3269_);
    crate::leanh::lean_dec_ref(v___y_3268_);
    crate::leanh::lean_dec(v___y_3267_);
    crate::leanh::lean_dec_ref(v___y_3266_);
    crate::leanh::lean_dec(v___y_3265_);
    crate::leanh::lean_dec_ref(v___y_3264_);
    return v_res_3271_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(
    mut v_upperBound_3272_: *mut crate::leanh::LeanObject,
    mut v___x_3273_: *mut crate::leanh::LeanObject,
    mut v_val_3274_: *mut crate::leanh::LeanObject,
    mut v_inst_3275_: *mut crate::leanh::LeanObject,
    mut v_R_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_b_3278_: *mut crate::leanh::LeanObject,
    mut v_c_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_3272_, v___x_3273_, v_val_3274_, v_a_3277_, v_b_3278_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
    return v___x_3287_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(
    mut v_upperBound_3288_: *mut crate::leanh::LeanObject,
    mut v___x_3289_: *mut crate::leanh::LeanObject,
    mut v_val_3290_: *mut crate::leanh::LeanObject,
    mut v_inst_3291_: *mut crate::leanh::LeanObject,
    mut v_R_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_b_3294_: *mut crate::leanh::LeanObject,
    mut v_c_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3303_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(
            v_upperBound_3288_,
            v___x_3289_,
            v_val_3290_,
            v_inst_3291_,
            v_R_3292_,
            v_a_3293_,
            v_b_3294_,
            v_c_3295_,
            v___y_3296_,
            v___y_3297_,
            v___y_3298_,
            v___y_3299_,
            v___y_3300_,
            v___y_3301_,
        );
    crate::leanh::lean_dec(v___y_3301_);
    crate::leanh::lean_dec_ref(v___y_3300_);
    crate::leanh::lean_dec(v___y_3299_);
    crate::leanh::lean_dec_ref(v___y_3298_);
    crate::leanh::lean_dec(v___y_3297_);
    crate::leanh::lean_dec_ref(v___y_3296_);
    crate::leanh::lean_dec_ref(v_val_3290_);
    crate::leanh::lean_dec(v___x_3289_);
    crate::leanh::lean_dec(v_upperBound_3288_);
    return v_res_3303_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_3307_, v___y_3308_, v___y_3309_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
    crate::leanh::lean_dec(v___y_3317_);
    crate::leanh::lean_dec_ref(v___y_3316_);
    crate::leanh::lean_dec(v___y_3315_);
    crate::leanh::lean_dec_ref(v___y_3314_);
    crate::leanh::lean_dec(v___y_3313_);
    crate::leanh::lean_dec_ref(v___y_3312_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_3325_);
    return v___x_3327_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    crate::leanh::lean_dec(v___y_3333_);
    crate::leanh::lean_dec_ref(v___y_3332_);
    crate::leanh::lean_dec(v___y_3331_);
    crate::leanh::lean_dec_ref(v___y_3330_);
    crate::leanh::lean_dec(v___y_3329_);
    crate::leanh::lean_dec_ref(v___y_3328_);
    return v_res_3335_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(
    mut v_00_u03b1_3336_: *mut crate::leanh::LeanObject,
    mut v_x_3337_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_3337_, v_ctx_x3f_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
    return v___x_3346_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(
    mut v_00_u03b1_3347_: *mut crate::leanh::LeanObject,
    mut v_x_3348_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_3347_, v_x_3348_, v_ctx_x3f_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
    crate::leanh::lean_dec(v___y_3355_);
    crate::leanh::lean_dec_ref(v___y_3354_);
    crate::leanh::lean_dec(v___y_3353_);
    crate::leanh::lean_dec_ref(v___y_3352_);
    crate::leanh::lean_dec(v___y_3351_);
    crate::leanh::lean_dec_ref(v___y_3350_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(
    mut v_00_u03b2_3358_: *mut crate::leanh::LeanObject,
    mut v_x_3359_: *mut crate::leanh::LeanObject,
    mut v_x_3360_: *mut crate::leanh::LeanObject,
    mut v_x_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_3359_, v_x_3360_, v_x_3361_);
    return v___x_3362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(
    mut v_00_u03b2_3363_: *mut crate::leanh::LeanObject,
    mut v_x_3364_: *mut crate::leanh::LeanObject,
    mut v_x_3365_: usize,
    mut v_x_3366_: usize,
    mut v_x_3367_: *mut crate::leanh::LeanObject,
    mut v_x_3368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3364_, v_x_3365_, v_x_3366_, v_x_3367_, v_x_3368_);
    return v___x_3369_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03b2_3370_: *mut crate::leanh::LeanObject,
    mut v_x_3371_: *mut crate::leanh::LeanObject,
    mut v_x_3372_: *mut crate::leanh::LeanObject,
    mut v_x_3373_: *mut crate::leanh::LeanObject,
    mut v_x_3374_: *mut crate::leanh::LeanObject,
    mut v_x_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_24820__boxed_3376_: usize = 0;
    let mut v_x_24821__boxed_3377_: usize = 0;
    let mut v_res_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_24820__boxed_3376_ = crate::leanh::lean_unbox_usize(v_x_3372_);
    crate::leanh::lean_dec(v_x_3372_);
    v_x_24821__boxed_3377_ = crate::leanh::lean_unbox_usize(v_x_3373_);
    crate::leanh::lean_dec(v_x_3373_);
    v_res_3378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_3370_, v_x_3371_, v_x_24820__boxed_3376_, v_x_24821__boxed_3377_, v_x_3374_, v_x_3375_);
    return v_res_3378_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(
    mut v_ref_3379_: *mut crate::leanh::LeanObject,
    mut v_msgData_3380_: *mut crate::leanh::LeanObject,
    mut v_severity_3381_: u8,
    mut v_isSilent_3382_: u8,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_3379_, v_msgData_3380_, v_severity_3381_, v_isSilent_3382_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    return v___x_3390_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(
    mut v_ref_3391_: *mut crate::leanh::LeanObject,
    mut v_msgData_3392_: *mut crate::leanh::LeanObject,
    mut v_severity_3393_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3402_: u8 = 0;
    let mut v_isSilent_boxed_3403_: u8 = 0;
    let mut v_res_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3402_ = (crate::leanh::lean_unbox(v_severity_3393_) as u8);
    v_isSilent_boxed_3403_ = (crate::leanh::lean_unbox(v_isSilent_3394_) as u8);
    v_res_3404_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_3391_, v_msgData_3392_, v_severity_boxed_3402_, v_isSilent_boxed_3403_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
    crate::leanh::lean_dec(v___y_3400_);
    crate::leanh::lean_dec_ref(v___y_3399_);
    crate::leanh::lean_dec(v___y_3398_);
    crate::leanh::lean_dec_ref(v___y_3397_);
    crate::leanh::lean_dec(v___y_3396_);
    crate::leanh::lean_dec_ref(v___y_3395_);
    crate::leanh::lean_dec(v_ref_3391_);
    return v_res_3404_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(
    mut v_00_u03b2_3405_: *mut crate::leanh::LeanObject,
    mut v_n_3406_: *mut crate::leanh::LeanObject,
    mut v_k_3407_: *mut crate::leanh::LeanObject,
    mut v_v_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_3406_, v_k_3407_, v_v_3408_);
    return v___x_3409_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(
    mut v_00_u03b2_3410_: *mut crate::leanh::LeanObject,
    mut v_depth_3411_: usize,
    mut v_keys_3412_: *mut crate::leanh::LeanObject,
    mut v_vals_3413_: *mut crate::leanh::LeanObject,
    mut v_heq_3414_: *mut crate::leanh::LeanObject,
    mut v_i_3415_: *mut crate::leanh::LeanObject,
    mut v_entries_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_3411_, v_keys_3412_, v_vals_3413_, v_i_3415_, v_entries_3416_);
    return v___x_3417_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(
    mut v_00_u03b2_3418_: *mut crate::leanh::LeanObject,
    mut v_depth_3419_: *mut crate::leanh::LeanObject,
    mut v_keys_3420_: *mut crate::leanh::LeanObject,
    mut v_vals_3421_: *mut crate::leanh::LeanObject,
    mut v_heq_3422_: *mut crate::leanh::LeanObject,
    mut v_i_3423_: *mut crate::leanh::LeanObject,
    mut v_entries_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3425_: usize = 0;
    let mut v_res_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3425_ = crate::leanh::lean_unbox_usize(v_depth_3419_);
    crate::leanh::lean_dec(v_depth_3419_);
    v_res_3426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_3418_, v_depth_boxed_3425_, v_keys_3420_, v_vals_3421_, v_heq_3422_, v_i_3423_, v_entries_3424_);
    crate::leanh::lean_dec_ref(v_vals_3421_);
    crate::leanh::lean_dec_ref(v_keys_3420_);
    return v_res_3426_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(
    mut v_00_u03b2_3427_: *mut crate::leanh::LeanObject,
    mut v_x_3428_: *mut crate::leanh::LeanObject,
    mut v_x_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: *mut crate::leanh::LeanObject,
    mut v_x_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_3428_, v_x_3429_, v_x_3430_, v_x_3431_);
    return v___x_3432_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(
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
pub unsafe fn initialize_Lean_Elab_Tactic_RenameInaccessibles(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
}
