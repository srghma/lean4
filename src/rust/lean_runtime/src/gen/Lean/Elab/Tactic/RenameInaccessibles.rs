// Lean compiler output
// Module: Lean.Elab.Tactic.RenameInaccessibles
// Imports: Lean.Elab.Term Lean.Elab.Binders
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_extractMacroScopes,
    l_Lean_replaceRef,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_11, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__1_value) as *mut LeanObject,13771926289831477797 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__3_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            116, 111, 111, 32, 109, 97, 110, 121, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 110,
            97, 109, 101, 115, 32, 112, 114, 111, 118, 105, 100, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_renameInaccessibles___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(
    mut v_x_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1719_);
    lean_inc_ref(v___y_1718_);
    v___x_1725_ = lean_apply_7(
        v_x_1717_,
        v___y_1718_,
        v___y_1719_,
        v___y_1720_,
        v___y_1721_,
        v___y_1722_,
        v___y_1723_,
        lean_box(0),
    );
    return v___x_1725_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed(
    mut v_x_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0(v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    return v_res_1734_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg(
    mut v_mvarId_1735_: *mut LeanObject,
    mut v_x_1736_: *mut LeanObject,
    mut v___y_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1749_: u8 = 0;
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1738_);
                lean_inc_ref(v___y_1737_);
                v___f_1744_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___f_1744_, 0, v_x_1736_);
                lean_closure_set(v___f_1744_, 1, v___y_1737_);
                lean_closure_set(v___f_1744_, 2, v___y_1738_);
                v___x_1745_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1735_,
                    v___f_1744_,
                    v___y_1739_,
                    v___y_1740_,
                    v___y_1741_,
                    v___y_1742_,
                );
                if lean_obj_tag(v___x_1745_) == 0 {
                    return v___x_1745_;
                } else {
                    v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
                    v_isSharedCheck_1753_ = (!lean_is_exclusive(v___x_1745_)) as u8;
                    if v_isSharedCheck_1753_ == 0 {
                        v___x_1748_ = v___x_1745_;
                        v_isShared_1749_ = v_isSharedCheck_1753_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1746_);
                        lean_dec(v___x_1745_);
                        v___x_1748_ = lean_box(0);
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
                    v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
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
    mut v_mvarId_1754_: *mut LeanObject,
    mut v_x_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1763_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1761_);
    lean_dec_ref(v___y_1760_);
    lean_dec(v___y_1759_);
    lean_dec_ref(v___y_1758_);
    lean_dec(v___y_1757_);
    lean_dec_ref(v___y_1756_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1(
    mut v_00_u03b1_1764_: *mut LeanObject,
    mut v_mvarId_1765_: *mut LeanObject,
    mut v_x_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
    mut v___y_1768_: *mut LeanObject,
    mut v___y_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_mvarId_1776_: *mut LeanObject,
    mut v_x_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1783_);
    lean_dec_ref(v___y_1782_);
    lean_dec(v___y_1781_);
    lean_dec_ref(v___y_1780_);
    lean_dec(v___y_1779_);
    lean_dec_ref(v___y_1778_);
    return v_res_1785_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(
    mut v_as_1786_: *mut LeanObject,
    mut v_sz_1787_: usize,
    mut v_i_1788_: usize,
    mut v_b_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: usize = 0;
    let mut v___x_1806_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1797_ = lean_usize_dec_lt(v_i_1788_, v_sz_1787_);
                if v___x_1797_ == 0 {
                    v___x_1798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1798_, 0, v_b_1789_);
                    return v___x_1798_;
                } else {
                    v_a_1799_ = lean_array_uget_borrowed(v_as_1786_, v_i_1788_);
                    v_fst_1800_ = lean_ctor_get(v_a_1799_, 0);
                    v_snd_1801_ = lean_ctor_get(v_a_1799_, 1);
                    lean_inc(v_fst_1800_);
                    v___x_1802_ = l_Lean_mkFVar(v_fst_1800_);
                    lean_inc(v_snd_1801_);
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
                    if lean_obj_tag(v___x_1803_) == 0 {
                        lean_dec_ref_known(v___x_1803_, 1);
                        v___x_1804_ = lean_box(0);
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
    mut v_as_1808_: *mut LeanObject,
    mut v_sz_1809_: *mut LeanObject,
    mut v_i_1810_: *mut LeanObject,
    mut v_b_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1819_: usize = 0;
    let mut v_i_boxed_1820_: usize = 0;
    let mut v_res_1821_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1819_ = lean_unbox_usize(v_sz_1809_);
    lean_dec(v_sz_1809_);
    v_i_boxed_1820_ = lean_unbox_usize(v_i_1810_);
    lean_dec(v_i_1810_);
    v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_as_1808_, v_sz_boxed_1819_, v_i_boxed_1820_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    lean_dec(v___y_1815_);
    lean_dec_ref(v___y_1814_);
    lean_dec(v___y_1813_);
    lean_dec_ref(v___y_1812_);
    lean_dec_ref(v_as_1808_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles___lam__0(
    mut v_fst_1822_: *mut LeanObject,
    mut v_sz_1823_: usize,
    mut v___x_1824_: usize,
    mut v___x_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__0(v_fst_1822_, v_sz_1823_, v___x_1824_, v___x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
                if lean_obj_tag(v___x_1833_) == 0 {
                    v_isSharedCheck_1840_ = (!lean_is_exclusive(v___x_1833_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v_unused_1841_ = lean_ctor_get(v___x_1833_, 0);
                        lean_dec(v_unused_1841_);
                        v___x_1835_ = v___x_1833_;
                        v_isShared_1836_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1833_);
                        v___x_1835_ = lean_box(0);
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
                    lean_ctor_set(v___x_1835_, 0, v___x_1825_);
                    v___x_1838_ = v___x_1835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1825_);
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
    mut v_fst_1842_: *mut LeanObject,
    mut v_sz_1843_: *mut LeanObject,
    mut v___x_1844_: *mut LeanObject,
    mut v___x_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1853_: usize = 0;
    let mut v___x_22490__boxed_1854_: usize = 0;
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1853_ = lean_unbox_usize(v_sz_1843_);
    lean_dec(v_sz_1843_);
    v___x_22490__boxed_1854_ = lean_unbox_usize(v___x_1844_);
    lean_dec(v___x_1844_);
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
    lean_dec(v___y_1851_);
    lean_dec_ref(v___y_1850_);
    lean_dec(v___y_1849_);
    lean_dec_ref(v___y_1848_);
    lean_dec(v___y_1847_);
    lean_dec_ref(v___y_1846_);
    lean_dec(v_fst_1842_);
    return v_res_1855_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___x_1856_ = lean_unsigned_to_nat(32);
    v___x_1857_ = lean_mk_empty_array_with_capacity(v___x_1856_);
    v___x_1858_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1859_: usize = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = 5usize;
    v___x_1860_ = lean_unsigned_to_nat(0);
    v___x_1861_ = lean_unsigned_to_nat(32);
    v___x_1862_ = lean_mk_empty_array_with_capacity(v___x_1861_);
    v___x_1863_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__0);
    v___x_1864_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1864_, 0, v___x_1863_);
    lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    lean_ctor_set(v___x_1864_, 2, v___x_1860_);
    lean_ctor_set(v___x_1864_, 3, v___x_1860_);
    lean_ctor_set_usize(v___x_1864_, 4, v___x_1859_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v_enabled_1883_: u8 = 0;
    let mut v_assignment_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v_unused_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1867_ = lean_st_ref_get(v___y_1865_);
                v_infoState_1868_ = lean_ctor_get(v___x_1867_, 7);
                lean_inc_ref(v_infoState_1868_);
                lean_dec(v___x_1867_);
                v_trees_1869_ = lean_ctor_get(v_infoState_1868_, 2);
                lean_inc_ref(v_trees_1869_);
                lean_dec_ref(v_infoState_1868_);
                v___x_1870_ = lean_st_ref_take(v___y_1865_);
                v_infoState_1871_ = lean_ctor_get(v___x_1870_, 7);
                v_env_1872_ = lean_ctor_get(v___x_1870_, 0);
                v_nextMacroScope_1873_ = lean_ctor_get(v___x_1870_, 1);
                v_ngen_1874_ = lean_ctor_get(v___x_1870_, 2);
                v_auxDeclNGen_1875_ = lean_ctor_get(v___x_1870_, 3);
                v_traceState_1876_ = lean_ctor_get(v___x_1870_, 4);
                v_cache_1877_ = lean_ctor_get(v___x_1870_, 5);
                v_messages_1878_ = lean_ctor_get(v___x_1870_, 6);
                v_snapshotTasks_1879_ = lean_ctor_get(v___x_1870_, 8);
                v_isSharedCheck_1900_ = (!lean_is_exclusive(v___x_1870_)) as u8;
                if v_isSharedCheck_1900_ == 0 {
                    v___x_1881_ = v___x_1870_;
                    v_isShared_1882_ = v_isSharedCheck_1900_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1879_);
                    lean_inc(v_infoState_1871_);
                    lean_inc(v_messages_1878_);
                    lean_inc(v_cache_1877_);
                    lean_inc(v_traceState_1876_);
                    lean_inc(v_auxDeclNGen_1875_);
                    lean_inc(v_ngen_1874_);
                    lean_inc(v_nextMacroScope_1873_);
                    lean_inc(v_env_1872_);
                    lean_dec(v___x_1870_);
                    v___x_1881_ = lean_box(0);
                    v_isShared_1882_ = v_isSharedCheck_1900_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1883_ = lean_ctor_get_uint8(
                    v_infoState_1871_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1884_ = lean_ctor_get(v_infoState_1871_, 0);
                v_lazyAssignment_1885_ = lean_ctor_get(v_infoState_1871_, 1);
                v_isSharedCheck_1898_ = (!lean_is_exclusive(v_infoState_1871_)) as u8;
                if v_isSharedCheck_1898_ == 0 {
                    v_unused_1899_ = lean_ctor_get(v_infoState_1871_, 2);
                    lean_dec(v_unused_1899_);
                    v___x_1887_ = v_infoState_1871_;
                    v_isShared_1888_ = v_isSharedCheck_1898_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1885_);
                    lean_inc(v_assignment_1884_);
                    lean_dec(v_infoState_1871_);
                    v___x_1887_ = lean_box(0);
                    v_isShared_1888_ = v_isSharedCheck_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___closed__1);
                if v_isShared_1888_ == 0 {
                    lean_ctor_set(v___x_1887_, 2, v___x_1889_);
                    v___x_1891_ = v___x_1887_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_assignment_1884_);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_lazyAssignment_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___x_1889_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1897_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1883_,
                    );
                    v___x_1891_ = v_reuseFailAlloc_1897_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1882_ == 0 {
                    lean_ctor_set(v___x_1881_, 7, v___x_1891_);
                    v___x_1893_ = v___x_1881_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_env_1872_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_nextMacroScope_1873_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_ngen_1874_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_auxDeclNGen_1875_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_traceState_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_cache_1877_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_messages_1878_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 7, v___x_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_snapshotTasks_1879_);
                    v___x_1893_ = v_reuseFailAlloc_1896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1894_ = lean_st_ref_set(v___y_1865_, v___x_1893_);
                v___x_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1895_, 0, v_trees_1869_);
                return v___x_1895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg___boxed(
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_1901_);
    lean_dec(v___y_1901_);
    return v_res_1903_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(
    mut v___x_1904_: *mut LeanObject,
    mut v_ctx_x3f_1905_: *mut LeanObject,
    mut v_sz_1906_: usize,
    mut v_i_1907_: usize,
    mut v_bs_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: usize = 0;
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1916_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
                if v___x_1916_ == 0 {
                    lean_dec_ref(v_ctx_x3f_1905_);
                    v___x_1917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1917_, 0, v_bs_1908_);
                    return v___x_1917_;
                } else {
                    v_assignment_1918_ = lean_ctor_get(v___x_1904_, 0);
                    lean_inc_ref(v_ctx_x3f_1905_);
                    lean_inc(v___y_1914_);
                    lean_inc_ref(v___y_1913_);
                    lean_inc(v___y_1912_);
                    lean_inc_ref(v___y_1911_);
                    lean_inc(v___y_1910_);
                    lean_inc_ref(v___y_1909_);
                    v___x_1919_ = lean_apply_7(
                        v_ctx_x3f_1905_,
                        v___y_1909_,
                        v___y_1910_,
                        v___y_1911_,
                        v___y_1912_,
                        v___y_1913_,
                        v___y_1914_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1919_) == 0 {
                        v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
                        lean_inc(v_a_1920_);
                        lean_dec_ref_known(v___x_1919_, 1);
                        v_v_1921_ = lean_array_uget(v_bs_1908_, v_i_1907_);
                        v___x_1922_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1923_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1922_);
                        v_tree_1930_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_1921_, v_assignment_1918_);
                        if lean_obj_tag(v_a_1920_) == 0 {
                            v_a_1925_ = v_tree_1930_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1931_ = lean_ctor_get(v_a_1920_, 0);
                            lean_inc(v_val_1931_);
                            lean_dec_ref_known(v_a_1920_, 1);
                            v___x_1932_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1932_, 0, v_val_1931_);
                            lean_ctor_set(v___x_1932_, 1, v_tree_1930_);
                            v_a_1925_ = v___x_1932_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_bs_1908_);
                        lean_dec_ref(v_ctx_x3f_1905_);
                        v_a_1933_ = lean_ctor_get(v___x_1919_, 0);
                        v_isSharedCheck_1940_ = (!lean_is_exclusive(v___x_1919_)) as u8;
                        if v_isSharedCheck_1940_ == 0 {
                            v___x_1935_ = v___x_1919_;
                            v_isShared_1936_ = v_isSharedCheck_1940_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1933_);
                            lean_dec(v___x_1919_);
                            v___x_1935_ = lean_box(0);
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
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
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
    mut v___x_1941_: *mut LeanObject,
    mut v_ctx_x3f_1942_: *mut LeanObject,
    mut v_sz_1943_: *mut LeanObject,
    mut v_i_1944_: *mut LeanObject,
    mut v_bs_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1953_: usize = 0;
    let mut v_i_boxed_1954_: usize = 0;
    let mut v_res_1955_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1943_);
    lean_dec(v_sz_1943_);
    v_i_boxed_1954_ = lean_unbox_usize(v_i_1944_);
    lean_dec(v_i_1944_);
    v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_1941_, v_ctx_x3f_1942_, v_sz_boxed_1953_, v_i_boxed_1954_, v_bs_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
    lean_dec(v___y_1951_);
    lean_dec_ref(v___y_1950_);
    lean_dec(v___y_1949_);
    lean_dec_ref(v___y_1948_);
    lean_dec(v___y_1947_);
    lean_dec_ref(v___y_1946_);
    lean_dec_ref(v___x_1941_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(
    mut v___x_1956_: *mut LeanObject,
    mut v_ctx_x3f_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_sz_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_isSharedCheck_1992_: u8 = 0;
    let mut v_vs_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v_sz_1997_: usize = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1958_) == 0 {
                    v_cs_1966_ = lean_ctor_get(v_x_1958_, 0);
                    v_isSharedCheck_1992_ = (!lean_is_exclusive(v_x_1958_)) as u8;
                    if v_isSharedCheck_1992_ == 0 {
                        v___x_1968_ = v_x_1958_;
                        v_isShared_1969_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_1966_);
                        lean_dec(v_x_1958_);
                        v___x_1968_ = lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1993_ = lean_ctor_get(v_x_1958_, 0);
                    v_isSharedCheck_2019_ = (!lean_is_exclusive(v_x_1958_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_1995_ = v_x_1958_;
                        v_isShared_1996_ = v_isSharedCheck_2019_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_vs_1993_);
                        lean_dec(v_x_1958_);
                        v___x_1995_ = lean_box(0);
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
                if lean_obj_tag(v___x_1972_) == 0 {
                    v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1983_ = (!lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_1983_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1973_);
                        lean_dec(v___x_1972_);
                        v___x_1975_ = lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1983_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1968_);
                    v_a_1984_ = lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1991_ = (!lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1986_ = v___x_1972_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1984_);
                        lean_dec(v___x_1972_);
                        v___x_1986_ = lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1969_ == 0 {
                    lean_ctor_set(v___x_1968_, 0, v_a_1973_);
                    v___x_1978_ = v___x_1968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1976_ == 0 {
                    lean_ctor_set(v___x_1975_, 0, v___x_1978_);
                    v___x_1980_ = v___x_1975_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
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
                    v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
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
                if lean_obj_tag(v___x_1999_) == 0 {
                    v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2010_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2002_ = v___x_1999_;
                        v_isShared_2003_ = v_isSharedCheck_2010_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2000_);
                        lean_dec(v___x_1999_);
                        v___x_2002_ = lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2010_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1995_);
                    v_a_2011_ = lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2018_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_1999_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2011_);
                        lean_dec(v___x_1999_);
                        v___x_2013_ = lean_box(0);
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1996_ == 0 {
                    lean_ctor_set(v___x_1995_, 0, v_a_2000_);
                    v___x_2005_ = v___x_1995_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2009_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2003_ == 0 {
                    lean_ctor_set(v___x_2002_, 0, v___x_2005_);
                    v___x_2007_ = v___x_2002_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
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
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
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
    mut v___x_2020_: *mut LeanObject,
    mut v_ctx_x3f_2021_: *mut LeanObject,
    mut v_sz_2022_: usize,
    mut v_i_2023_: usize,
    mut v_bs_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2032_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
                if v___x_2032_ == 0 {
                    lean_dec_ref(v_ctx_x3f_2021_);
                    v___x_2033_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2033_, 0, v_bs_2024_);
                    return v___x_2033_;
                } else {
                    v_v_2034_ = lean_array_uget_borrowed(v_bs_2024_, v_i_2023_);
                    lean_inc(v_v_2034_);
                    lean_inc_ref(v_ctx_x3f_2021_);
                    v___x_2035_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2020_, v_ctx_x3f_2021_, v_v_2034_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
                    if lean_obj_tag(v___x_2035_) == 0 {
                        v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
                        lean_inc(v_a_2036_);
                        lean_dec_ref_known(v___x_2035_, 1);
                        v___x_2037_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2038_ = lean_array_uset(v_bs_2024_, v_i_2023_, v___x_2037_);
                        v___x_2039_ = 1usize;
                        v___x_2040_ = lean_usize_add(v_i_2023_, v___x_2039_);
                        v___x_2041_ = lean_array_uset(v_bs_x27_2038_, v_i_2023_, v_a_2036_);
                        v_i_2023_ = v___x_2040_;
                        v_bs_2024_ = v___x_2041_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2024_);
                        lean_dec_ref(v_ctx_x3f_2021_);
                        v_a_2043_ = lean_ctor_get(v___x_2035_, 0);
                        v_isSharedCheck_2050_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v___x_2045_ = v___x_2035_;
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2043_);
                            lean_dec(v___x_2035_);
                            v___x_2045_ = lean_box(0);
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
                    v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
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
    mut v___x_2051_: *mut LeanObject,
    mut v_ctx_x3f_2052_: *mut LeanObject,
    mut v_sz_2053_: *mut LeanObject,
    mut v_i_2054_: *mut LeanObject,
    mut v_bs_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2063_: usize = 0;
    let mut v_i_boxed_2064_: usize = 0;
    let mut v_res_2065_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2053_);
    lean_dec(v_sz_2053_);
    v_i_boxed_2064_ = lean_unbox_usize(v_i_2054_);
    lean_dec(v_i_2054_);
    v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11_spec__14(v___x_2051_, v_ctx_x3f_2052_, v_sz_boxed_2063_, v_i_boxed_2064_, v_bs_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
    lean_dec(v___y_2061_);
    lean_dec_ref(v___y_2060_);
    lean_dec(v___y_2059_);
    lean_dec_ref(v___y_2058_);
    lean_dec(v___y_2057_);
    lean_dec_ref(v___y_2056_);
    lean_dec_ref(v___x_2051_);
    return v_res_2065_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11___boxed(
    mut v___x_2066_: *mut LeanObject,
    mut v_ctx_x3f_2067_: *mut LeanObject,
    mut v_x_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2076_: *mut LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2066_, v_ctx_x3f_2067_, v_x_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
    lean_dec(v___y_2074_);
    lean_dec_ref(v___y_2073_);
    lean_dec(v___y_2072_);
    lean_dec_ref(v___y_2071_);
    lean_dec(v___y_2070_);
    lean_dec_ref(v___y_2069_);
    lean_dec_ref(v___x_2066_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(
    mut v___x_2077_: *mut LeanObject,
    mut v_ctx_x3f_2078_: *mut LeanObject,
    mut v_t_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_2090_: usize = 0;
    let mut v_tailOff_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2097_: usize = 0;
    let mut v___x_2098_: usize = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_a_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2087_ = lean_ctor_get(v_t_2079_, 0);
                v_tail_2088_ = lean_ctor_get(v_t_2079_, 1);
                v_size_2089_ = lean_ctor_get(v_t_2079_, 2);
                v_shift_2090_ = lean_ctor_get_usize(v_t_2079_, 4);
                v_tailOff_2091_ = lean_ctor_get(v_t_2079_, 3);
                v_isSharedCheck_2127_ = (!lean_is_exclusive(v_t_2079_)) as u8;
                if v_isSharedCheck_2127_ == 0 {
                    v___x_2093_ = v_t_2079_;
                    v_isShared_2094_ = v_isSharedCheck_2127_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_2091_);
                    lean_inc(v_size_2089_);
                    lean_inc(v_tail_2088_);
                    lean_inc(v_root_2087_);
                    lean_dec(v_t_2079_);
                    v___x_2093_ = lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_ctx_x3f_2078_);
                v___x_2095_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__11(v___x_2077_, v_ctx_x3f_2078_, v_root_2087_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
                if lean_obj_tag(v___x_2095_) == 0 {
                    v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
                    lean_inc(v_a_2096_);
                    lean_dec_ref_known(v___x_2095_, 1);
                    v_sz_2097_ = lean_array_size(v_tail_2088_);
                    v___x_2098_ = 0usize;
                    v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6_spec__12(v___x_2077_, v_ctx_x3f_2078_, v_sz_2097_, v___x_2098_, v_tail_2088_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
                    if lean_obj_tag(v___x_2099_) == 0 {
                        v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
                        v_isSharedCheck_2110_ = (!lean_is_exclusive(v___x_2099_)) as u8;
                        if v_isSharedCheck_2110_ == 0 {
                            v___x_2102_ = v___x_2099_;
                            v_isShared_2103_ = v_isSharedCheck_2110_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2100_);
                            lean_dec(v___x_2099_);
                            v___x_2102_ = lean_box(0);
                            v_isShared_2103_ = v_isSharedCheck_2110_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2096_);
                        lean_del_object(v___x_2093_);
                        lean_dec(v_tailOff_2091_);
                        lean_dec(v_size_2089_);
                        v_a_2111_ = lean_ctor_get(v___x_2099_, 0);
                        v_isSharedCheck_2118_ = (!lean_is_exclusive(v___x_2099_)) as u8;
                        if v_isSharedCheck_2118_ == 0 {
                            v___x_2113_ = v___x_2099_;
                            v_isShared_2114_ = v_isSharedCheck_2118_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2111_);
                            lean_dec(v___x_2099_);
                            v___x_2113_ = lean_box(0);
                            v_isShared_2114_ = v_isSharedCheck_2118_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2093_);
                    lean_dec(v_tailOff_2091_);
                    lean_dec(v_size_2089_);
                    lean_dec_ref(v_tail_2088_);
                    lean_dec_ref(v_ctx_x3f_2078_);
                    v_a_2119_ = lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2126_ = (!lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2126_ == 0 {
                        v___x_2121_ = v___x_2095_;
                        v_isShared_2122_ = v_isSharedCheck_2126_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2119_);
                        lean_dec(v___x_2095_);
                        v___x_2121_ = lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2126_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2094_ == 0 {
                    lean_ctor_set(v___x_2093_, 1, v_a_2100_);
                    lean_ctor_set(v___x_2093_, 0, v_a_2096_);
                    v___x_2105_ = v___x_2093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2096_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_a_2100_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_size_2089_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_tailOff_2091_);
                    lean_ctor_set_usize(v_reuseFailAlloc_2109_, 4, v_shift_2090_);
                    v___x_2105_ = v_reuseFailAlloc_2109_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2103_ == 0 {
                    lean_ctor_set(v___x_2102_, 0, v___x_2105_);
                    v___x_2107_ = v___x_2102_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
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
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
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
                    v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
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
    mut v___x_2128_: *mut LeanObject,
    mut v_ctx_x3f_2129_: *mut LeanObject,
    mut v_t_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2138_: *mut LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v___x_2128_, v_ctx_x3f_2129_, v_t_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
    lean_dec(v___y_2136_);
    lean_dec_ref(v___y_2135_);
    lean_dec(v___y_2134_);
    lean_dec_ref(v___y_2133_);
    lean_dec(v___y_2132_);
    lean_dec_ref(v___y_2131_);
    lean_dec_ref(v___x_2128_);
    return v_res_2138_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(
    mut v___y_2139_: *mut LeanObject,
    mut v_ctx_x3f_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v_a_2146_: *mut LeanObject,
    mut v_a_x3f_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v_enabled_2170_: u8 = 0;
    let mut v_assignment_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_unused_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2149_ = lean_st_ref_get(v___y_2139_);
                v_infoState_2150_ = lean_ctor_get(v___x_2149_, 7);
                lean_inc_ref(v_infoState_2150_);
                lean_dec(v___x_2149_);
                v_trees_2151_ = lean_ctor_get(v_infoState_2150_, 2);
                lean_inc_ref(v_trees_2151_);
                v___x_2152_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__6(v_infoState_2150_, v_ctx_x3f_2140_, v_trees_2151_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2139_);
                lean_dec_ref(v_infoState_2150_);
                if lean_obj_tag(v___x_2152_) == 0 {
                    v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2191_ = (!lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2155_ = v___x_2152_;
                        v_isShared_2156_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2153_);
                        lean_dec(v___x_2152_);
                        v___x_2155_ = lean_box(0);
                        v_isShared_2156_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_2146_);
                    v_a_2192_ = lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2199_ = (!lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2199_ == 0 {
                        v___x_2194_ = v___x_2152_;
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2192_);
                        lean_dec(v___x_2152_);
                        v___x_2194_ = lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2199_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2157_ = lean_st_ref_take(v___y_2139_);
                v_infoState_2158_ = lean_ctor_get(v___x_2157_, 7);
                v_env_2159_ = lean_ctor_get(v___x_2157_, 0);
                v_nextMacroScope_2160_ = lean_ctor_get(v___x_2157_, 1);
                v_ngen_2161_ = lean_ctor_get(v___x_2157_, 2);
                v_auxDeclNGen_2162_ = lean_ctor_get(v___x_2157_, 3);
                v_traceState_2163_ = lean_ctor_get(v___x_2157_, 4);
                v_cache_2164_ = lean_ctor_get(v___x_2157_, 5);
                v_messages_2165_ = lean_ctor_get(v___x_2157_, 6);
                v_snapshotTasks_2166_ = lean_ctor_get(v___x_2157_, 8);
                v_isSharedCheck_2190_ = (!lean_is_exclusive(v___x_2157_)) as u8;
                if v_isSharedCheck_2190_ == 0 {
                    v___x_2168_ = v___x_2157_;
                    v_isShared_2169_ = v_isSharedCheck_2190_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2166_);
                    lean_inc(v_infoState_2158_);
                    lean_inc(v_messages_2165_);
                    lean_inc(v_cache_2164_);
                    lean_inc(v_traceState_2163_);
                    lean_inc(v_auxDeclNGen_2162_);
                    lean_inc(v_ngen_2161_);
                    lean_inc(v_nextMacroScope_2160_);
                    lean_inc(v_env_2159_);
                    lean_dec(v___x_2157_);
                    v___x_2168_ = lean_box(0);
                    v_isShared_2169_ = v_isSharedCheck_2190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_2170_ = lean_ctor_get_uint8(
                    v_infoState_2158_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_2171_ = lean_ctor_get(v_infoState_2158_, 0);
                v_lazyAssignment_2172_ = lean_ctor_get(v_infoState_2158_, 1);
                v_isSharedCheck_2188_ = (!lean_is_exclusive(v_infoState_2158_)) as u8;
                if v_isSharedCheck_2188_ == 0 {
                    v_unused_2189_ = lean_ctor_get(v_infoState_2158_, 2);
                    lean_dec(v_unused_2189_);
                    v___x_2174_ = v_infoState_2158_;
                    v_isShared_2175_ = v_isSharedCheck_2188_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_2172_);
                    lean_inc(v_assignment_2171_);
                    lean_dec(v_infoState_2158_);
                    v___x_2174_ = lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2176_ = l_Lean_PersistentArray_append___redArg(v_a_2146_, v_a_2153_);
                lean_dec(v_a_2153_);
                if v_isShared_2175_ == 0 {
                    lean_ctor_set(v___x_2174_, 2, v___x_2176_);
                    v___x_2178_ = v___x_2174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_assignment_2171_);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_lazyAssignment_2172_);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2176_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2187_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_2170_,
                    );
                    v___x_2178_ = v_reuseFailAlloc_2187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2169_ == 0 {
                    lean_ctor_set(v___x_2168_, 7, v___x_2178_);
                    v___x_2180_ = v___x_2168_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_env_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_nextMacroScope_2160_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_ngen_2161_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_auxDeclNGen_2162_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_traceState_2163_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 5, v_cache_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 6, v_messages_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 7, v___x_2178_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 8, v_snapshotTasks_2166_);
                    v___x_2180_ = v_reuseFailAlloc_2186_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2181_ = lean_st_ref_set(v___y_2139_, v___x_2180_);
                v___x_2182_ = lean_box(0);
                if v_isShared_2156_ == 0 {
                    lean_ctor_set(v___x_2155_, 0, v___x_2182_);
                    v___x_2184_ = v___x_2155_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
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
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
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
    mut v___y_2200_: *mut LeanObject,
    mut v_ctx_x3f_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_x3f_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2200_, v_ctx_x3f_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v_a_2207_, v_a_x3f_2208_);
    lean_dec(v_a_x3f_2208_);
    lean_dec_ref(v___y_2206_);
    lean_dec(v___y_2205_);
    lean_dec_ref(v___y_2204_);
    lean_dec(v___y_2203_);
    lean_dec_ref(v___y_2202_);
    lean_dec(v___y_2200_);
    return v_res_2210_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(
    mut v_x_2211_: *mut LeanObject,
    mut v_ctx_x3f_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2222_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_unused_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_reuseFailAlloc_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_unused_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_st_ref_get(v___y_2218_);
                v_infoState_2221_ = lean_ctor_get(v___x_2220_, 7);
                lean_inc_ref(v_infoState_2221_);
                lean_dec(v___x_2220_);
                v_enabled_2222_ = lean_ctor_get_uint8(
                    v_infoState_2221_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_2221_);
                if v_enabled_2222_ == 0 {
                    lean_dec_ref(v_ctx_x3f_2212_);
                    lean_inc(v___y_2218_);
                    lean_inc_ref(v___y_2217_);
                    lean_inc(v___y_2216_);
                    lean_inc_ref(v___y_2215_);
                    lean_inc(v___y_2214_);
                    lean_inc_ref(v___y_2213_);
                    v___x_2223_ = lean_apply_7(
                        v_x_2211_,
                        v___y_2213_,
                        v___y_2214_,
                        v___y_2215_,
                        v___y_2216_,
                        v___y_2217_,
                        v___y_2218_,
                        lean_box(0),
                    );
                    return v___x_2223_;
                } else {
                    v___x_2224_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_2218_);
                    v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
                    lean_inc(v_a_2225_);
                    lean_dec_ref(v___x_2224_);
                    lean_inc(v___y_2218_);
                    lean_inc_ref(v___y_2217_);
                    lean_inc(v___y_2216_);
                    lean_inc_ref(v___y_2215_);
                    lean_inc(v___y_2214_);
                    lean_inc_ref(v___y_2213_);
                    v_r_2226_ = lean_apply_7(
                        v_x_2211_,
                        v___y_2213_,
                        v___y_2214_,
                        v___y_2215_,
                        v___y_2216_,
                        v___y_2217_,
                        v___y_2218_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_2226_) == 0 {
                        v_a_2227_ = lean_ctor_get(v_r_2226_, 0);
                        v_isSharedCheck_2251_ = (!lean_is_exclusive(v_r_2226_)) as u8;
                        if v_isSharedCheck_2251_ == 0 {
                            v___x_2229_ = v_r_2226_;
                            v_isShared_2230_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2227_);
                            lean_dec(v_r_2226_);
                            v___x_2229_ = lean_box(0);
                            v_isShared_2230_ = v_isSharedCheck_2251_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2252_ = lean_ctor_get(v_r_2226_, 0);
                        lean_inc(v_a_2252_);
                        lean_dec_ref_known(v_r_2226_, 1);
                        v___x_2253_ = lean_box(0);
                        v___x_2254_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2218_, v_ctx_x3f_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v_a_2225_, v___x_2253_);
                        if lean_obj_tag(v___x_2254_) == 0 {
                            v_isSharedCheck_2261_ = (!lean_is_exclusive(v___x_2254_)) as u8;
                            if v_isSharedCheck_2261_ == 0 {
                                v_unused_2262_ = lean_ctor_get(v___x_2254_, 0);
                                lean_dec(v_unused_2262_);
                                v___x_2256_ = v___x_2254_;
                                v_isShared_2257_ = v_isSharedCheck_2261_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_2254_);
                                v___x_2256_ = lean_box(0);
                                v_isShared_2257_ = v_isSharedCheck_2261_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2252_);
                            v_a_2263_ = lean_ctor_get(v___x_2254_, 0);
                            v_isSharedCheck_2270_ = (!lean_is_exclusive(v___x_2254_)) as u8;
                            if v_isSharedCheck_2270_ == 0 {
                                v___x_2265_ = v___x_2254_;
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2263_);
                                lean_dec(v___x_2254_);
                                v___x_2265_ = lean_box(0);
                                v_isShared_2266_ = v_isSharedCheck_2270_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_2227_);
                if v_isShared_2230_ == 0 {
                    lean_ctor_set_tag(v___x_2229_, 1);
                    v___x_2232_ = v___x_2229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2227_);
                    v___x_2232_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2233_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg___lam__0(v___y_2218_, v_ctx_x3f_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v_a_2225_, v___x_2232_);
                lean_dec_ref(v___x_2232_);
                if lean_obj_tag(v___x_2233_) == 0 {
                    v_isSharedCheck_2240_ = (!lean_is_exclusive(v___x_2233_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v_unused_2241_ = lean_ctor_get(v___x_2233_, 0);
                        lean_dec(v_unused_2241_);
                        v___x_2235_ = v___x_2233_;
                        v_isShared_2236_ = v_isSharedCheck_2240_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2233_);
                        v___x_2235_ = lean_box(0);
                        v_isShared_2236_ = v_isSharedCheck_2240_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2227_);
                    v_a_2242_ = lean_ctor_get(v___x_2233_, 0);
                    v_isSharedCheck_2249_ = (!lean_is_exclusive(v___x_2233_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v___x_2233_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2242_);
                        lean_dec(v___x_2233_);
                        v___x_2244_ = lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2236_ == 0 {
                    lean_ctor_set(v___x_2235_, 0, v_a_2227_);
                    v___x_2238_ = v___x_2235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2227_);
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
                    v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
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
                    lean_ctor_set_tag(v___x_2256_, 1);
                    lean_ctor_set(v___x_2256_, 0, v_a_2252_);
                    v___x_2259_ = v___x_2256_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2252_);
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
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
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
    mut v_x_2271_: *mut LeanObject,
    mut v_ctx_x3f_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_2271_, v_ctx_x3f_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    lean_dec(v___y_2276_);
    lean_dec_ref(v___y_2275_);
    lean_dec(v___y_2274_);
    lean_dec_ref(v___y_2273_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    v___x_2285_ = lean_st_ref_get(v___y_2283_);
    v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
    lean_inc_ref(v_env_2286_);
    lean_dec(v___x_2285_);
    v___x_2287_ = lean_st_ref_get(v___y_2281_);
    v_mctx_2288_ = lean_ctor_get(v___x_2287_, 0);
    lean_inc_ref(v_mctx_2288_);
    lean_dec(v___x_2287_);
    v_options_2289_ = lean_ctor_get(v___y_2282_, 2);
    v_currNamespace_2290_ = lean_ctor_get(v___y_2282_, 6);
    v_openDecls_2291_ = lean_ctor_get(v___y_2282_, 7);
    v___x_2292_ = lean_st_ref_get(v___y_2283_);
    v_ngen_2293_ = lean_ctor_get(v___x_2292_, 2);
    lean_inc_ref(v_ngen_2293_);
    lean_dec(v___x_2292_);
    v___x_2294_ = lean_box(0);
    v___x_2295_ = l_Lean_instInhabitedFileMap_default;
    lean_inc(v_openDecls_2291_);
    lean_inc(v_currNamespace_2290_);
    lean_inc_ref(v_options_2289_);
    v___x_2296_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_2296_, 0, v_env_2286_);
    lean_ctor_set(v___x_2296_, 1, v___x_2294_);
    lean_ctor_set(v___x_2296_, 2, v___x_2295_);
    lean_ctor_set(v___x_2296_, 3, v_mctx_2288_);
    lean_ctor_set(v___x_2296_, 4, v_options_2289_);
    lean_ctor_set(v___x_2296_, 5, v_currNamespace_2290_);
    lean_ctor_set(v___x_2296_, 6, v_openDecls_2291_);
    lean_ctor_set(v___x_2296_, 7, v_ngen_2293_);
    v___x_2297_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2297_, 0, v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg___boxed(
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2302_: *mut LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_2298_, v___y_2299_, v___y_2300_);
    lean_dec(v___y_2300_);
    lean_dec_ref(v___y_2299_);
    lean_dec(v___y_2298_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v_fileMap_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut v_unused_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2310_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_2306_, v___y_2307_, v___y_2308_);
                v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
                v_isSharedCheck_2335_ = (!lean_is_exclusive(v___x_2310_)) as u8;
                if v_isSharedCheck_2335_ == 0 {
                    v___x_2313_ = v___x_2310_;
                    v_isShared_2314_ = v_isSharedCheck_2335_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2311_);
                    lean_dec(v___x_2310_);
                    v___x_2313_ = lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2335_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_2315_ = lean_ctor_get(v___y_2307_, 1);
                v_env_2316_ = lean_ctor_get(v_a_2311_, 0);
                v_mctx_2317_ = lean_ctor_get(v_a_2311_, 3);
                v_options_2318_ = lean_ctor_get(v_a_2311_, 4);
                v_currNamespace_2319_ = lean_ctor_get(v_a_2311_, 5);
                v_openDecls_2320_ = lean_ctor_get(v_a_2311_, 6);
                v_ngen_2321_ = lean_ctor_get(v_a_2311_, 7);
                v_isSharedCheck_2332_ = (!lean_is_exclusive(v_a_2311_)) as u8;
                if v_isSharedCheck_2332_ == 0 {
                    v_unused_2333_ = lean_ctor_get(v_a_2311_, 2);
                    lean_dec(v_unused_2333_);
                    v_unused_2334_ = lean_ctor_get(v_a_2311_, 1);
                    lean_dec(v_unused_2334_);
                    v___x_2323_ = v_a_2311_;
                    v_isShared_2324_ = v_isSharedCheck_2332_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ngen_2321_);
                    lean_inc(v_openDecls_2320_);
                    lean_inc(v_currNamespace_2319_);
                    lean_inc(v_options_2318_);
                    lean_inc(v_mctx_2317_);
                    lean_inc(v_env_2316_);
                    lean_dec(v_a_2311_);
                    v___x_2323_ = lean_box(0);
                    v_isShared_2324_ = v_isSharedCheck_2332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2325_ = lean_box(0);
                lean_inc_ref(v_fileMap_2315_);
                if v_isShared_2324_ == 0 {
                    lean_ctor_set(v___x_2323_, 2, v_fileMap_2315_);
                    lean_ctor_set(v___x_2323_, 1, v___x_2325_);
                    v___x_2327_ = v___x_2323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_env_2316_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2325_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_fileMap_2315_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_mctx_2317_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_options_2318_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 5, v_currNamespace_2319_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 6, v_openDecls_2320_);
                    lean_ctor_set(v_reuseFailAlloc_2331_, 7, v_ngen_2321_);
                    v___x_2327_ = v_reuseFailAlloc_2331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2314_ == 0 {
                    lean_ctor_set(v___x_2313_, 0, v___x_2327_);
                    v___x_2329_ = v___x_2313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
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
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    lean_dec(v___y_2341_);
    lean_dec_ref(v___y_2340_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2(v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
                v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
                v_isSharedCheck_2361_ = (!lean_is_exclusive(v___x_2351_)) as u8;
                if v_isSharedCheck_2361_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    v_isShared_2355_ = v_isSharedCheck_2361_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2352_);
                    lean_dec(v___x_2351_);
                    v___x_2354_ = lean_box(0);
                    v_isShared_2355_ = v_isSharedCheck_2361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2356_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2356_, 0, v_a_2352_);
                v___x_2357_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2357_, 0, v___x_2356_);
                if v_isShared_2355_ == 0 {
                    lean_ctor_set(v___x_2354_, 0, v___x_2357_);
                    v___x_2359_ = v___x_2354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
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
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___lam__0(v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
    lean_dec(v___y_2367_);
    lean_dec_ref(v___y_2366_);
    lean_dec(v___y_2365_);
    lean_dec_ref(v___y_2364_);
    lean_dec(v___y_2363_);
    lean_dec_ref(v___y_2362_);
    return v_res_2369_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(
    mut v_x_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
    mut v___y_2375_: *mut LeanObject,
    mut v___y_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___f_2379_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___closed__0;
    v___x_2380_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_2371_, v___f_2379_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
    return v___x_2380_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg___boxed(
    mut v_x_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
    lean_dec(v___y_2387_);
    lean_dec_ref(v___y_2386_);
    lean_dec(v___y_2385_);
    lean_dec_ref(v___y_2384_);
    lean_dec(v___y_2383_);
    lean_dec_ref(v___y_2382_);
    return v_res_2389_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(
    mut v_snd_2390_: *mut LeanObject,
    mut v___x_2391_: *mut LeanObject,
    mut v_____r_2392_: *mut LeanObject,
    mut v_lctx_2393_: *mut LeanObject,
    mut v_hs_2394_: *mut LeanObject,
    mut v_info_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_NameSet_insert(v_snd_2390_, v___x_2391_);
    v___x_2404_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2404_, 0, v_info_2395_);
    lean_ctor_set(v___x_2404_, 1, v___x_2403_);
    v___x_2405_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2405_, 0, v_hs_2394_);
    lean_ctor_set(v___x_2405_, 1, v___x_2404_);
    v___x_2406_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2406_, 0, v_lctx_2393_);
    lean_ctor_set(v___x_2406_, 1, v___x_2405_);
    v___x_2407_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2407_, 0, v___x_2406_);
    v___x_2408_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2408_, 0, v___x_2407_);
    return v___x_2408_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed(
    mut v_snd_2409_: *mut LeanObject,
    mut v___x_2410_: *mut LeanObject,
    mut v_____r_2411_: *mut LeanObject,
    mut v_lctx_2412_: *mut LeanObject,
    mut v_hs_2413_: *mut LeanObject,
    mut v_info_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2422_: *mut LeanObject = core::ptr::null_mut();
    v_res_2422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_2409_, v___x_2410_, v_____r_2411_, v_lctx_2412_, v_hs_2413_, v_info_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
    lean_dec(v___y_2420_);
    lean_dec_ref(v___y_2419_);
    lean_dec(v___y_2418_);
    lean_dec_ref(v___y_2417_);
    lean_dec(v___y_2416_);
    lean_dec_ref(v___y_2415_);
    return v_res_2422_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(
    mut v_fst_2423_: *mut LeanObject,
    mut v___f_2424_: *mut LeanObject,
    mut v_snd_2425_: *mut LeanObject,
    mut v_____r_2426_: *mut LeanObject,
    mut v_lctx_2427_: *mut LeanObject,
    mut v_info_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    v___x_2436_ = lean_array_pop(v_fst_2423_);
    v___x_2437_ = lean_array_get_size(v___x_2436_);
    v___x_2438_ = lean_unsigned_to_nat(0);
    v___x_2439_ = lean_nat_dec_eq(v___x_2437_, v___x_2438_);
    if v___x_2439_ == 0 {
        let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_snd_2425_);
        v___x_2440_ = lean_box(0);
        lean_inc(v___y_2434_);
        lean_inc_ref(v___y_2433_);
        lean_inc(v___y_2432_);
        lean_inc_ref(v___y_2431_);
        lean_inc(v___y_2430_);
        lean_inc_ref(v___y_2429_);
        v___x_2441_ = lean_apply_11(
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
            lean_box(0),
        );
        return v___x_2441_;
    } else {
        let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_2424_);
        v___x_2442_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2442_, 0, v_info_2428_);
        lean_ctor_set(v___x_2442_, 1, v_snd_2425_);
        v___x_2443_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2443_, 0, v___x_2436_);
        lean_ctor_set(v___x_2443_, 1, v___x_2442_);
        v___x_2444_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2444_, 0, v_lctx_2427_);
        lean_ctor_set(v___x_2444_, 1, v___x_2443_);
        v___x_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2445_, 0, v___x_2444_);
        v___x_2446_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2446_, 0, v___x_2445_);
        return v___x_2446_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1___boxed(
    mut v_fst_2447_: *mut LeanObject,
    mut v___f_2448_: *mut LeanObject,
    mut v_snd_2449_: *mut LeanObject,
    mut v_____r_2450_: *mut LeanObject,
    mut v_lctx_2451_: *mut LeanObject,
    mut v_info_2452_: *mut LeanObject,
    mut v___y_2453_: *mut LeanObject,
    mut v___y_2454_: *mut LeanObject,
    mut v___y_2455_: *mut LeanObject,
    mut v___y_2456_: *mut LeanObject,
    mut v___y_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2460_: *mut LeanObject = core::ptr::null_mut();
    v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2447_, v___f_2448_, v_snd_2449_, v_____r_2450_, v_lctx_2451_, v_info_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
    lean_dec(v___y_2458_);
    lean_dec_ref(v___y_2457_);
    lean_dec(v___y_2456_);
    lean_dec_ref(v___y_2455_);
    lean_dec(v___y_2454_);
    lean_dec_ref(v___y_2453_);
    return v_res_2460_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(
    mut v_upperBound_2469_: *mut LeanObject,
    mut v___x_2470_: *mut LeanObject,
    mut v_val_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_b_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v_a_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_a_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v_fst_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v_fst_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_unused_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v_unused_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2506_ = lean_nat_dec_lt(v_a_2472_, v_upperBound_2469_);
                if v___x_2506_ == 0 {
                    lean_dec(v_a_2472_);
                    v___x_2507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2507_, 0, v_b_2473_);
                    return v___x_2507_;
                } else {
                    v_snd_2508_ = lean_ctor_get(v_b_2473_, 1);
                    lean_inc(v_snd_2508_);
                    v_snd_2509_ = lean_ctor_get(v_snd_2508_, 1);
                    lean_inc(v_snd_2509_);
                    v_fst_2510_ = lean_ctor_get(v_b_2473_, 0);
                    v_isSharedCheck_2581_ = (!lean_is_exclusive(v_b_2473_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v_unused_2582_ = lean_ctor_get(v_b_2473_, 1);
                        lean_dec(v_unused_2582_);
                        v___x_2512_ = v_b_2473_;
                        v_isShared_2513_ = v_isSharedCheck_2581_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_fst_2510_);
                        lean_dec(v_b_2473_);
                        v___x_2512_ = lean_box(0);
                        v_isShared_2513_ = v_isSharedCheck_2581_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2483_ = lean_unsigned_to_nat(1);
                v___x_2484_ = lean_nat_add(v_a_2472_, v___x_2483_);
                lean_dec(v_a_2472_);
                v_a_2472_ = v___x_2484_;
                v_b_2473_ = v_a_2482_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_2487_) == 0 {
                    v_a_2488_ = lean_ctor_get(v___y_2487_, 0);
                    v_isSharedCheck_2497_ = (!lean_is_exclusive(v___y_2487_)) as u8;
                    if v_isSharedCheck_2497_ == 0 {
                        v___x_2490_ = v___y_2487_;
                        v_isShared_2491_ = v_isSharedCheck_2497_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2488_);
                        lean_dec(v___y_2487_);
                        v___x_2490_ = lean_box(0);
                        v_isShared_2491_ = v_isSharedCheck_2497_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2472_);
                    v_a_2498_ = lean_ctor_get(v___y_2487_, 0);
                    v_isSharedCheck_2505_ = (!lean_is_exclusive(v___y_2487_)) as u8;
                    if v_isSharedCheck_2505_ == 0 {
                        v___x_2500_ = v___y_2487_;
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2498_);
                        lean_dec(v___y_2487_);
                        v___x_2500_ = lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_2488_) == 0 {
                    lean_dec(v_a_2472_);
                    v_a_2492_ = lean_ctor_get(v_a_2488_, 0);
                    lean_inc(v_a_2492_);
                    lean_dec_ref_known(v_a_2488_, 1);
                    if v_isShared_2491_ == 0 {
                        lean_ctor_set(v___x_2490_, 0, v_a_2492_);
                        v___x_2494_ = v___x_2490_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2492_);
                        v___x_2494_ = v_reuseFailAlloc_2495_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2490_);
                    v_a_2496_ = lean_ctor_get(v_a_2488_, 0);
                    lean_inc(v_a_2496_);
                    lean_dec_ref_known(v_a_2488_, 1);
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
                    v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
                    v___x_2503_ = v_reuseFailAlloc_2504_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2503_;
            }
            7 => {
                v_fst_2514_ = lean_ctor_get(v_snd_2508_, 0);
                v_isSharedCheck_2579_ = (!lean_is_exclusive(v_snd_2508_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v_unused_2580_ = lean_ctor_get(v_snd_2508_, 1);
                    lean_dec(v_unused_2580_);
                    v___x_2516_ = v_snd_2508_;
                    v_isShared_2517_ = v_isSharedCheck_2579_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_fst_2514_);
                    lean_dec(v_snd_2508_);
                    v___x_2516_ = lean_box(0);
                    v_isShared_2517_ = v_isSharedCheck_2579_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_2518_ = lean_ctor_get(v_snd_2509_, 0);
                v_snd_2519_ = lean_ctor_get(v_snd_2509_, 1);
                v_isSharedCheck_2578_ = (!lean_is_exclusive(v_snd_2509_)) as u8;
                if v_isSharedCheck_2578_ == 0 {
                    v___x_2521_ = v_snd_2509_;
                    v_isShared_2522_ = v_isSharedCheck_2578_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_snd_2519_);
                    lean_inc(v_fst_2518_);
                    lean_dec(v_snd_2509_);
                    v___x_2521_ = lean_box(0);
                    v_isShared_2522_ = v_isSharedCheck_2578_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2523_ = lean_nat_sub(v___x_2470_, v_a_2472_);
                v___x_2524_ = lean_unsigned_to_nat(1);
                v___x_2525_ = lean_nat_sub(v___x_2523_, v___x_2524_);
                lean_dec(v___x_2523_);
                v___x_2526_ = l_Lean_LocalContext_getAt_x3f(v_fst_2510_, v___x_2525_);
                lean_dec(v___x_2525_);
                if lean_obj_tag(v___x_2526_) == 0 {
                    if v_isShared_2522_ == 0 {
                        v___x_2528_ = v___x_2521_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_fst_2518_);
                        lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_snd_2519_);
                        v___x_2528_ = v_reuseFailAlloc_2535_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_val_2536_ = lean_ctor_get(v___x_2526_, 0);
                    lean_inc(v_val_2536_);
                    lean_dec_ref_known(v___x_2526_, 1);
                    v___x_2537_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2536_);
                    if v___x_2537_ == 0 {
                        lean_del_object(v___x_2516_);
                        lean_del_object(v___x_2512_);
                        v___x_2538_ = l_Lean_LocalDecl_userName(v_val_2536_);
                        lean_inc_n(v___x_2538_, 2);
                        lean_inc(v_snd_2519_);
                        v___f_2539_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                        lean_closure_set(v___f_2539_, 0, v_snd_2519_);
                        lean_closure_set(v___f_2539_, 1, v___x_2538_);
                        v___x_2564_ = l_Lean_extractMacroScopes(v___x_2538_);
                        v___x_2565_ = l_Lean_MacroScopesView_equalScope(v___x_2564_, v_val_2471_);
                        lean_dec_ref(v___x_2564_);
                        if v___x_2565_ == 0 {
                            lean_dec(v___x_2538_);
                            state = 13;
                            continue;
                        } else {
                            if v___x_2537_ == 0 {
                                v___x_2566_ = l_Lean_NameSet_contains(v_snd_2519_, v___x_2538_);
                                if v___x_2566_ == 0 {
                                    lean_dec_ref(v___f_2539_);
                                    lean_dec(v_val_2536_);
                                    lean_del_object(v___x_2521_);
                                    v___x_2567_ = lean_box(0);
                                    v___x_2568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__0(v_snd_2519_, v___x_2538_, v___x_2567_, v_fst_2510_, v_fst_2514_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                                    v___y_2487_ = v___x_2568_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v___x_2538_);
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2538_);
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_2536_);
                        if v_isShared_2522_ == 0 {
                            v___x_2570_ = v___x_2521_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_fst_2518_);
                            lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2519_);
                            v___x_2570_ = v_reuseFailAlloc_2577_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_2517_ == 0 {
                    lean_ctor_set(v___x_2516_, 1, v___x_2528_);
                    v___x_2530_ = v___x_2516_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_fst_2514_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2534_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2513_ == 0 {
                    lean_ctor_set(v___x_2512_, 1, v___x_2530_);
                    v___x_2532_ = v___x_2512_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fst_2510_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
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
                v___x_2542_ = lean_box(0);
                v___x_2543_ = lean_array_get_size(v_fst_2514_);
                v___x_2544_ = lean_nat_sub(v___x_2543_, v___x_2524_);
                v___x_2545_ = lean_array_get_borrowed(v___x_2542_, v_fst_2514_, v___x_2544_);
                lean_dec(v___x_2544_);
                lean_inc(v___x_2545_);
                v___x_2546_ = l_Lean_Syntax_isOfKind(v___x_2545_, v___x_2541_);
                if v___x_2546_ == 0 {
                    lean_dec(v_val_2536_);
                    lean_del_object(v___x_2521_);
                    v___x_2547_ = lean_box(0);
                    v___x_2548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2547_, v_fst_2510_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                    v___y_2487_ = v___x_2548_;
                    state = 2;
                    continue;
                } else {
                    v___x_2549_ = lean_unsigned_to_nat(0);
                    v___x_2550_ = l_Lean_Syntax_getArg(v___x_2545_, v___x_2549_);
                    v___x_2551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4;
                    lean_inc(v___x_2550_);
                    v___x_2552_ = l_Lean_Syntax_isOfKind(v___x_2550_, v___x_2551_);
                    if v___x_2552_ == 0 {
                        lean_dec(v___x_2550_);
                        lean_dec(v_val_2536_);
                        lean_del_object(v___x_2521_);
                        v___x_2553_ = lean_box(0);
                        v___x_2554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2553_, v_fst_2510_, v_fst_2518_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                        v___y_2487_ = v___x_2554_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2555_ = l_Lean_TSyntax_getId(v___x_2550_);
                        v___x_2556_ = l_Lean_LocalDecl_fvarId(v_val_2536_);
                        lean_dec(v_val_2536_);
                        lean_inc(v___x_2556_);
                        v___x_2557_ =
                            l_Lean_LocalContext_setUserName(v_fst_2510_, v___x_2556_, v___x_2555_);
                        if v_isShared_2522_ == 0 {
                            lean_ctor_set(v___x_2521_, 1, v___x_2550_);
                            lean_ctor_set(v___x_2521_, 0, v___x_2556_);
                            v___x_2559_ = v___x_2521_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2556_);
                            lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2550_);
                            v___x_2559_ = v_reuseFailAlloc_2563_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                v___x_2560_ = lean_array_push(v_fst_2518_, v___x_2559_);
                v___x_2561_ = lean_box(0);
                v___x_2562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___lam__1(v_fst_2514_, v___f_2539_, v_snd_2519_, v___x_2561_, v___x_2557_, v___x_2560_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
                v___y_2487_ = v___x_2562_;
                state = 2;
                continue;
            }
            15 => {
                if v_isShared_2517_ == 0 {
                    lean_ctor_set(v___x_2516_, 1, v___x_2570_);
                    v___x_2572_ = v___x_2516_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2514_);
                    lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2570_);
                    v___x_2572_ = v_reuseFailAlloc_2576_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2513_ == 0 {
                    lean_ctor_set(v___x_2512_, 1, v___x_2572_);
                    v___x_2574_ = v___x_2512_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2510_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2572_);
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
    mut v_upperBound_2583_: *mut LeanObject,
    mut v___x_2584_: *mut LeanObject,
    mut v_val_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_b_2587_: *mut LeanObject,
    mut v___y_2588_: *mut LeanObject,
    mut v___y_2589_: *mut LeanObject,
    mut v___y_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2595_: *mut LeanObject = core::ptr::null_mut();
    v_res_2595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_2583_, v___x_2584_, v_val_2585_, v_a_2586_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
    lean_dec(v___y_2593_);
    lean_dec_ref(v___y_2592_);
    lean_dec(v___y_2591_);
    lean_dec_ref(v___y_2590_);
    lean_dec(v___y_2589_);
    lean_dec_ref(v___y_2588_);
    lean_dec_ref(v_val_2585_);
    lean_dec(v___x_2584_);
    lean_dec(v_upperBound_2583_);
    return v_res_2595_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(
    mut v___y_2604_: u8,
    mut v_suppressElabErrors_2605_: u8,
    mut v_x_2606_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2606_) == 1 {
        let mut v_pre_2607_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2607_ = lean_ctor_get(v_x_2606_, 0);
        match lean_obj_tag(v_pre_2607_) {
            1 => {
                let mut v_pre_2608_: *mut LeanObject = core::ptr::null_mut();
                v_pre_2608_ = lean_ctor_get(v_pre_2607_, 0);
                match lean_obj_tag(v_pre_2608_) {
                    0 => {
                        let mut v_str_2609_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_2610_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2612_: u8 = 0;
                        v_str_2609_ = lean_ctor_get(v_x_2606_, 1);
                        v_str_2610_ = lean_ctor_get(v_pre_2607_, 1);
                        v___x_2611_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__0;
                        v___x_2612_ = lean_string_dec_eq(v_str_2610_, v___x_2611_);
                        if v___x_2612_ == 0 {
                            let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2614_: u8 = 0;
                            v___x_2613_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__1;
                            v___x_2614_ = lean_string_dec_eq(v_str_2610_, v___x_2613_);
                            if v___x_2614_ == 0 {
                                return v___y_2604_;
                            } else {
                                let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_2619_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_2619_ = lean_ctor_get(v_pre_2608_, 0);
                        if lean_obj_tag(v_pre_2619_) == 0 {
                            let mut v_str_2620_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2621_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2622_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2624_: u8 = 0;
                            v_str_2620_ = lean_ctor_get(v_x_2606_, 1);
                            v_str_2621_ = lean_ctor_get(v_pre_2607_, 1);
                            v_str_2622_ = lean_ctor_get(v_pre_2608_, 1);
                            v___x_2623_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__4;
                            v___x_2624_ = lean_string_dec_eq(v_str_2622_, v___x_2623_);
                            if v___x_2624_ == 0 {
                                return v___y_2604_;
                            } else {
                                let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2626_: u8 = 0;
                                v___x_2625_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___closed__5;
                                v___x_2626_ = lean_string_dec_eq(v_str_2621_, v___x_2625_);
                                if v___x_2626_ == 0 {
                                    return v___y_2604_;
                                } else {
                                    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_2629_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2631_: u8 = 0;
                v_str_2629_ = lean_ctor_get(v_x_2606_, 1);
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
    mut v___y_2632_: *mut LeanObject,
    mut v_suppressElabErrors_2633_: *mut LeanObject,
    mut v_x_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23688__boxed_2635_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2636_: u8 = 0;
    let mut v_res_2637_: u8 = 0;
    let mut v_r_2638_: *mut LeanObject = core::ptr::null_mut();
    v___y_23688__boxed_2635_ = (lean_unbox(v___y_2632_) as u8);
    v_suppressElabErrors_boxed_2636_ = (lean_unbox(v_suppressElabErrors_2633_) as u8);
    v_res_2637_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0(v___y_23688__boxed_2635_, v_suppressElabErrors_boxed_2636_, v_x_2634_);
    lean_dec(v_x_2634_);
    v_r_2638_ = lean_box((v_res_2637_) as usize);
    return v_r_2638_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(
    mut v_opts_2639_: *mut LeanObject,
    mut v_opt_2640_: *mut LeanObject,
) -> u8 {
    let mut v_name_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v_name_2641_ = lean_ctor_get(v_opt_2640_, 0);
    v_defValue_2642_ = lean_ctor_get(v_opt_2640_, 1);
    v_map_2643_ = lean_ctor_get(v_opts_2639_, 0);
    v___x_2644_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2643_,
            v_name_2641_,
        );
    if lean_obj_tag(v___x_2644_) == 0 {
        let mut v___x_2645_: u8 = 0;
        v___x_2645_ = (lean_unbox(v_defValue_2642_) as u8);
        return v___x_2645_;
    } else {
        let mut v_val_2646_: *mut LeanObject = core::ptr::null_mut();
        v_val_2646_ = lean_ctor_get(v___x_2644_, 0);
        lean_inc(v_val_2646_);
        lean_dec_ref_known(v___x_2644_, 1);
        if lean_obj_tag(v_val_2646_) == 1 {
            let mut v_v_2647_: u8 = 0;
            v_v_2647_ = lean_ctor_get_uint8(v_val_2646_, 0 as u32);
            lean_dec_ref_known(v_val_2646_, 0);
            return v_v_2647_;
        } else {
            let mut v___x_2648_: u8 = 0;
            lean_dec(v_val_2646_);
            v___x_2648_ = (lean_unbox(v_defValue_2642_) as u8);
            return v___x_2648_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20___boxed(
    mut v_opts_2649_: *mut LeanObject,
    mut v_opt_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2651_: u8 = 0;
    let mut v_r_2652_: *mut LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__20(v_opts_2649_, v_opt_2650_);
    lean_dec_ref(v_opt_2650_);
    lean_dec_ref(v_opts_2649_);
    v_r_2652_ = lean_box((v_res_2651_) as usize);
    return v_r_2652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(
    mut v_msgData_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    v___x_2659_ = lean_st_ref_get(v___y_2657_);
    v_env_2660_ = lean_ctor_get(v___x_2659_, 0);
    lean_inc_ref(v_env_2660_);
    lean_dec(v___x_2659_);
    v___x_2661_ = lean_st_ref_get(v___y_2655_);
    v_mctx_2662_ = lean_ctor_get(v___x_2661_, 0);
    lean_inc_ref(v_mctx_2662_);
    lean_dec(v___x_2661_);
    v_lctx_2663_ = lean_ctor_get(v___y_2654_, 2);
    v_options_2664_ = lean_ctor_get(v___y_2656_, 2);
    lean_inc_ref(v_options_2664_);
    lean_inc_ref(v_lctx_2663_);
    v___x_2665_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2665_, 0, v_env_2660_);
    lean_ctor_set(v___x_2665_, 1, v_mctx_2662_);
    lean_ctor_set(v___x_2665_, 2, v_lctx_2663_);
    lean_ctor_set(v___x_2665_, 3, v_options_2664_);
    v___x_2666_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2666_, 0, v___x_2665_);
    lean_ctor_set(v___x_2666_, 1, v_msgData_2653_);
    v___x_2667_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2667_, 0, v___x_2666_);
    return v___x_2667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19___boxed(
    mut v_msgData_2668_: *mut LeanObject,
    mut v___y_2669_: *mut LeanObject,
    mut v___y_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2674_: *mut LeanObject = core::ptr::null_mut();
    v_res_2674_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v_msgData_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
    lean_dec(v___y_2672_);
    lean_dec_ref(v___y_2671_);
    lean_dec(v___y_2670_);
    lean_dec_ref(v___y_2669_);
    return v_res_2674_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(
    mut v_ref_2676_: *mut LeanObject,
    mut v_msgData_2677_: *mut LeanObject,
    mut v_severity_2678_: u8,
    mut v_isSilent_2679_: u8,
    mut v___y_2680_: *mut LeanObject,
    mut v___y_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: u8 = 0;
    let mut v___y_2690_: u8 = 0;
    let mut v___y_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v___y_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: u8 = 0;
    let mut v___y_2727_: u8 = 0;
    let mut v___y_2728_: u8 = 0;
    let mut v___y_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v___y_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: u8 = 0;
    let mut v___y_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: u8 = 0;
    let mut v___y_2753_: u8 = 0;
    let mut v___y_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: u8 = 0;
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: u8 = 0;
    let mut v_ref_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___y_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: u8 = 0;
    let mut v___y_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: u8 = 0;
    let mut v___y_2777_: u8 = 0;
    let mut v___y_2779_: u8 = 0;
    let mut v_fileName_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2784_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_2677_);
                    v___x_2795_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2677_);
                    v___y_2779_ = v___x_2795_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2695_ = lean_st_ref_take(v___y_2694_);
                v_currNamespace_2696_ = lean_ctor_get(v___y_2693_, 6);
                v_openDecls_2697_ = lean_ctor_get(v___y_2693_, 7);
                v_env_2698_ = lean_ctor_get(v___x_2695_, 0);
                v_nextMacroScope_2699_ = lean_ctor_get(v___x_2695_, 1);
                v_ngen_2700_ = lean_ctor_get(v___x_2695_, 2);
                v_auxDeclNGen_2701_ = lean_ctor_get(v___x_2695_, 3);
                v_traceState_2702_ = lean_ctor_get(v___x_2695_, 4);
                v_cache_2703_ = lean_ctor_get(v___x_2695_, 5);
                v_messages_2704_ = lean_ctor_get(v___x_2695_, 6);
                v_infoState_2705_ = lean_ctor_get(v___x_2695_, 7);
                v_snapshotTasks_2706_ = lean_ctor_get(v___x_2695_, 8);
                v_isSharedCheck_2720_ = (!lean_is_exclusive(v___x_2695_)) as u8;
                if v_isSharedCheck_2720_ == 0 {
                    v___x_2708_ = v___x_2695_;
                    v_isShared_2709_ = v_isSharedCheck_2720_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2706_);
                    lean_inc(v_infoState_2705_);
                    lean_inc(v_messages_2704_);
                    lean_inc(v_cache_2703_);
                    lean_inc(v_traceState_2702_);
                    lean_inc(v_auxDeclNGen_2701_);
                    lean_inc(v_ngen_2700_);
                    lean_inc(v_nextMacroScope_2699_);
                    lean_inc(v_env_2698_);
                    lean_dec(v___x_2695_);
                    v___x_2708_ = lean_box(0);
                    v_isShared_2709_ = v_isSharedCheck_2720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_2697_);
                lean_inc(v_currNamespace_2696_);
                v___x_2710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2710_, 0, v_currNamespace_2696_);
                lean_ctor_set(v___x_2710_, 1, v_openDecls_2697_);
                v___x_2711_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2711_, 0, v___x_2710_);
                lean_ctor_set(v___x_2711_, 1, v___y_2686_);
                lean_inc_ref(v___y_2691_);
                lean_inc_ref(v___y_2688_);
                v___x_2712_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2712_, 0, v___y_2688_);
                lean_ctor_set(v___x_2712_, 1, v___y_2692_);
                lean_ctor_set(v___x_2712_, 2, v___y_2687_);
                lean_ctor_set(v___x_2712_, 3, v___y_2691_);
                lean_ctor_set(v___x_2712_, 4, v___x_2711_);
                lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2690_,
                );
                lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2689_,
                );
                lean_ctor_set_uint8(
                    v___x_2712_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2679_,
                );
                v___x_2713_ = l_Lean_MessageLog_add(v___x_2712_, v_messages_2704_);
                if v_isShared_2709_ == 0 {
                    lean_ctor_set(v___x_2708_, 6, v___x_2713_);
                    v___x_2715_ = v___x_2708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_env_2698_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_nextMacroScope_2699_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_ngen_2700_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 3, v_auxDeclNGen_2701_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_traceState_2702_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 5, v_cache_2703_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 6, v___x_2713_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 7, v_infoState_2705_);
                    lean_ctor_set(v_reuseFailAlloc_2719_, 8, v_snapshotTasks_2706_);
                    v___x_2715_ = v_reuseFailAlloc_2719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2716_ = lean_st_ref_set(v___y_2694_, v___x_2715_);
                v___x_2717_ = lean_box(0);
                v___x_2718_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2718_, 0, v___x_2717_);
                return v___x_2718_;
            }
            4 => {
                v___x_2730_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2677_,
                    );
                v___x_2731_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12_spec__19(v___x_2730_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
                v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
                v_isSharedCheck_2745_ = (!lean_is_exclusive(v___x_2731_)) as u8;
                if v_isSharedCheck_2745_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    v_isShared_2735_ = v_isSharedCheck_2745_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_2732_);
                    lean_dec(v___x_2731_);
                    v___x_2734_ = lean_box(0);
                    v_isShared_2735_ = v_isSharedCheck_2745_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_2724_, 2);
                v___x_2736_ = l_Lean_FileMap_toPosition(v___y_2724_, v___y_2723_);
                lean_dec(v___y_2723_);
                v___x_2737_ = l_Lean_FileMap_toPosition(v___y_2724_, v___y_2729_);
                lean_dec(v___y_2729_);
                v___x_2738_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2738_, 0, v___x_2737_);
                v___x_2739_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___closed__0;
                if v___y_2728_ == 0 {
                    lean_del_object(v___x_2734_);
                    lean_dec_ref(v___y_2722_);
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
                    lean_inc(v_a_2732_);
                    v___x_2740_ = l_Lean_MessageData_hasTag(v___y_2722_, v_a_2732_);
                    if v___x_2740_ == 0 {
                        lean_dec_ref_known(v___x_2738_, 1);
                        lean_dec_ref(v___x_2736_);
                        lean_dec(v_a_2732_);
                        v___x_2741_ = lean_box(0);
                        if v_isShared_2735_ == 0 {
                            lean_ctor_set(v___x_2734_, 0, v___x_2741_);
                            v___x_2743_ = v___x_2734_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
                            v___x_2743_ = v_reuseFailAlloc_2744_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2734_);
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
                lean_dec(v___y_2751_);
                if lean_obj_tag(v___x_2755_) == 0 {
                    lean_inc(v___y_2754_);
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
                    v_val_2756_ = lean_ctor_get(v___x_2755_, 0);
                    lean_inc(v_val_2756_);
                    lean_dec_ref_known(v___x_2755_, 1);
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
                if lean_obj_tag(v___x_2766_) == 0 {
                    v___x_2767_ = lean_unsigned_to_nat(0);
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
                    v_val_2768_ = lean_ctor_get(v___x_2766_, 0);
                    lean_inc(v_val_2768_);
                    lean_dec_ref_known(v___x_2766_, 1);
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
                    v_fileName_2780_ = lean_ctor_get(v___y_2682_, 0);
                    v_fileMap_2781_ = lean_ctor_get(v___y_2682_, 1);
                    v_options_2782_ = lean_ctor_get(v___y_2682_, 2);
                    v_ref_2783_ = lean_ctor_get(v___y_2682_, 5);
                    v_suppressElabErrors_2784_ = lean_ctor_get_uint8(
                        v___y_2682_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2785_ = lean_box((v___y_2779_) as usize);
                    v___x_2786_ = lean_box((v_suppressElabErrors_2784_) as usize);
                    v___f_2787_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2787_, 0, v___x_2785_);
                    lean_closure_set(v___f_2787_, 1, v___x_2786_);
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
                    lean_dec_ref(v_msgData_2677_);
                    v___x_2792_ = lean_box(0);
                    v___x_2793_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2793_, 0, v___x_2792_);
                    return v___x_2793_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg___boxed(
    mut v_ref_2796_: *mut LeanObject,
    mut v_msgData_2797_: *mut LeanObject,
    mut v_severity_2798_: *mut LeanObject,
    mut v_isSilent_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
    mut v___y_2802_: *mut LeanObject,
    mut v___y_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2805_: u8 = 0;
    let mut v_isSilent_boxed_2806_: u8 = 0;
    let mut v_res_2807_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2805_ = (lean_unbox(v_severity_2798_) as u8);
    v_isSilent_boxed_2806_ = (lean_unbox(v_isSilent_2799_) as u8);
    v_res_2807_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_2796_, v_msgData_2797_, v_severity_boxed_2805_, v_isSilent_boxed_2806_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
    lean_dec(v___y_2803_);
    lean_dec_ref(v___y_2802_);
    lean_dec(v___y_2801_);
    lean_dec_ref(v___y_2800_);
    lean_dec(v_ref_2796_);
    return v_res_2807_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(
    mut v_msgData_2808_: *mut LeanObject,
    mut v_severity_2809_: u8,
    mut v_isSilent_2810_: u8,
    mut v___y_2811_: *mut LeanObject,
    mut v___y_2812_: *mut LeanObject,
    mut v___y_2813_: *mut LeanObject,
    mut v___y_2814_: *mut LeanObject,
    mut v___y_2815_: *mut LeanObject,
    mut v___y_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2818_ = lean_ctor_get(v___y_2815_, 5);
    v___x_2819_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_2818_, v_msgData_2808_, v_severity_2809_, v_isSilent_2810_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
    return v___x_2819_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7___boxed(
    mut v_msgData_2820_: *mut LeanObject,
    mut v_severity_2821_: *mut LeanObject,
    mut v_isSilent_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2830_: u8 = 0;
    let mut v_isSilent_boxed_2831_: u8 = 0;
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2830_ = (lean_unbox(v_severity_2821_) as u8);
    v_isSilent_boxed_2831_ = (lean_unbox(v_isSilent_2822_) as u8);
    v_res_2832_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_2820_, v_severity_boxed_2830_, v_isSilent_boxed_2831_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
    lean_dec(v___y_2828_);
    lean_dec_ref(v___y_2827_);
    lean_dec(v___y_2826_);
    lean_dec_ref(v___y_2825_);
    lean_dec(v___y_2824_);
    lean_dec_ref(v___y_2823_);
    return v_res_2832_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(
    mut v_msgData_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = 2;
    v___x_2842_ = 0;
    v___x_2843_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7(v_msgData_2833_, v___x_2841_, v___x_2842_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
    return v___x_2843_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4___boxed(
    mut v_msgData_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
    mut v___y_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2852_: *mut LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4(
        v_msgData_2844_,
        v___y_2845_,
        v___y_2846_,
        v___y_2847_,
        v___y_2848_,
        v___y_2849_,
        v___y_2850_,
    );
    lean_dec(v___y_2850_);
    lean_dec_ref(v___y_2849_);
    lean_dec(v___y_2848_);
    lean_dec_ref(v___y_2847_);
    lean_dec(v___y_2846_);
    lean_dec_ref(v___y_2845_);
    return v_res_2852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(
    mut v_as_2856_: *mut LeanObject,
    mut v_sz_2857_: usize,
    mut v_i_2858_: usize,
    mut v_b_2859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2865_ = lean_usize_dec_lt(v_i_2858_, v_sz_2857_);
                if v___x_2865_ == 0 {
                    lean_inc_ref(v_b_2859_);
                    return v_b_2859_;
                } else {
                    v___x_2866_ = lean_box(0);
                    v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0;
                    v_a_2868_ = lean_array_uget_borrowed(v_as_2856_, v_i_2858_);
                    v___x_2869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__2;
                    lean_inc(v_a_2868_);
                    v___x_2870_ = l_Lean_Syntax_isOfKind(v_a_2868_, v___x_2869_);
                    if v___x_2870_ == 0 {
                        v_a_2861_ = v___x_2867_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2871_ = lean_unsigned_to_nat(0);
                        v___x_2872_ = l_Lean_Syntax_getArg(v_a_2868_, v___x_2871_);
                        v___x_2873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg___closed__4;
                        lean_inc(v___x_2872_);
                        v___x_2874_ = l_Lean_Syntax_isOfKind(v___x_2872_, v___x_2873_);
                        if v___x_2874_ == 0 {
                            lean_dec(v___x_2872_);
                            v_a_2861_ = v___x_2867_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2875_ = l_Lean_TSyntax_getId(v___x_2872_);
                            lean_dec(v___x_2872_);
                            v___x_2876_ = l_Lean_extractMacroScopes(v___x_2875_);
                            v___x_2877_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2877_, 0, v___x_2876_);
                            v___x_2878_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2878_, 0, v___x_2877_);
                            v___x_2879_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2879_, 0, v___x_2878_);
                            lean_ctor_set(v___x_2879_, 1, v___x_2866_);
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
    mut v_as_2880_: *mut LeanObject,
    mut v_sz_2881_: *mut LeanObject,
    mut v_i_2882_: *mut LeanObject,
    mut v_b_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2884_: usize = 0;
    let mut v_i_boxed_2885_: usize = 0;
    let mut v_res_2886_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2884_ = lean_unbox_usize(v_sz_2881_);
    lean_dec(v_sz_2881_);
    v_i_boxed_2885_ = lean_unbox_usize(v_i_2882_);
    lean_dec(v_i_2882_);
    v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_as_2880_, v_sz_boxed_2884_, v_i_boxed_2885_, v_b_2883_);
    lean_dec_ref(v_b_2883_);
    lean_dec_ref(v_as_2880_);
    return v_res_2886_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(
    mut v_x_2887_: *mut LeanObject,
    mut v_x_2888_: *mut LeanObject,
    mut v_x_2889_: *mut LeanObject,
    mut v_x_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2891_ = lean_ctor_get(v_x_2887_, 0);
                v_vs_2892_ = lean_ctor_get(v_x_2887_, 1);
                v_isSharedCheck_2916_ = (!lean_is_exclusive(v_x_2887_)) as u8;
                if v_isSharedCheck_2916_ == 0 {
                    v___x_2894_ = v_x_2887_;
                    v_isShared_2895_ = v_isSharedCheck_2916_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2892_);
                    lean_inc(v_ks_2891_);
                    lean_dec(v_x_2887_);
                    v___x_2894_ = lean_box(0);
                    v_isShared_2895_ = v_isSharedCheck_2916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2896_ = lean_array_get_size(v_ks_2891_);
                v___x_2897_ = lean_nat_dec_lt(v_x_2888_, v___x_2896_);
                if v___x_2897_ == 0 {
                    lean_dec(v_x_2888_);
                    v___x_2898_ = lean_array_push(v_ks_2891_, v_x_2889_);
                    v___x_2899_ = lean_array_push(v_vs_2892_, v_x_2890_);
                    if v_isShared_2895_ == 0 {
                        lean_ctor_set(v___x_2894_, 1, v___x_2899_);
                        lean_ctor_set(v___x_2894_, 0, v___x_2898_);
                        v___x_2901_ = v___x_2894_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2898_);
                        lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2899_);
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
                            v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_ks_2891_);
                            lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_vs_2892_);
                            v___x_2906_ = v_reuseFailAlloc_2910_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2911_ = lean_array_fset(v_ks_2891_, v_x_2888_, v_x_2889_);
                        v___x_2912_ = lean_array_fset(v_vs_2892_, v_x_2888_, v_x_2890_);
                        lean_dec(v_x_2888_);
                        if v_isShared_2895_ == 0 {
                            lean_ctor_set(v___x_2894_, 1, v___x_2912_);
                            lean_ctor_set(v___x_2894_, 0, v___x_2911_);
                            v___x_2914_ = v___x_2894_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2911_);
                            lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2912_);
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
                v___x_2907_ = lean_unsigned_to_nat(1);
                v___x_2908_ = lean_nat_add(v_x_2888_, v___x_2907_);
                lean_dec(v_x_2888_);
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
    mut v_n_2917_: *mut LeanObject,
    mut v_k_2918_: *mut LeanObject,
    mut v_v_2919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    v___x_2920_ = lean_unsigned_to_nat(0);
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
    v___x_2926_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__0);
    v___x_2927_ = lean_usize_sub(v___x_2926_, v___x_2925_);
    return v___x_2927_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    v___x_2928_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2928_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(
    mut v_x_2929_: *mut LeanObject,
    mut v_x_2930_: usize,
    mut v_x_2931_: usize,
    mut v_x_2932_: *mut LeanObject,
    mut v_x_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: usize = 0;
    let mut v___x_2936_: usize = 0;
    let mut v___x_2937_: usize = 0;
    let mut v___x_2938_: usize = 0;
    let mut v_j_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v_v_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_node_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: usize = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_unused_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: u8 = 0;
    let mut v_ks_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: usize = 0;
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u8 = 0;
    let mut v_reuseFailAlloc_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2929_) == 0 {
                    v_es_2934_ = lean_ctor_get(v_x_2929_, 0);
                    v___x_2935_ = 5usize;
                    v___x_2936_ = 1usize;
                    v___x_2937_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__1);
                    v___x_2938_ = lean_usize_land(v_x_2930_, v___x_2937_);
                    v_j_2939_ = lean_usize_to_nat(v___x_2938_);
                    v___x_2940_ = lean_array_get_size(v_es_2934_);
                    v___x_2941_ = lean_nat_dec_lt(v_j_2939_, v___x_2940_);
                    if v___x_2941_ == 0 {
                        lean_dec(v_j_2939_);
                        lean_dec(v_x_2933_);
                        lean_dec(v_x_2932_);
                        return v_x_2929_;
                    } else {
                        lean_inc_ref(v_es_2934_);
                        v_isSharedCheck_2978_ = (!lean_is_exclusive(v_x_2929_)) as u8;
                        if v_isSharedCheck_2978_ == 0 {
                            v_unused_2979_ = lean_ctor_get(v_x_2929_, 0);
                            lean_dec(v_unused_2979_);
                            v___x_2943_ = v_x_2929_;
                            v_isShared_2944_ = v_isSharedCheck_2978_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2929_);
                            v___x_2943_ = lean_box(0);
                            v_isShared_2944_ = v_isSharedCheck_2978_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2980_ = lean_ctor_get(v_x_2929_, 0);
                    v_vs_2981_ = lean_ctor_get(v_x_2929_, 1);
                    v_isSharedCheck_3001_ = (!lean_is_exclusive(v_x_2929_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2983_ = v_x_2929_;
                        v_isShared_2984_ = v_isSharedCheck_3001_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2981_);
                        lean_inc(v_ks_2980_);
                        lean_dec(v_x_2929_);
                        v___x_2983_ = lean_box(0);
                        v_isShared_2984_ = v_isSharedCheck_3001_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2945_ = lean_array_fget(v_es_2934_, v_j_2939_);
                v___x_2946_ = lean_box(0);
                v_xs_x27_2947_ = lean_array_fset(v_es_2934_, v_j_2939_, v___x_2946_);
                match lean_obj_tag(v_v_2945_) {
                    0 => {
                        v_key_2954_ = lean_ctor_get(v_v_2945_, 0);
                        v_val_2955_ = lean_ctor_get(v_v_2945_, 1);
                        v_isSharedCheck_2965_ = (!lean_is_exclusive(v_v_2945_)) as u8;
                        if v_isSharedCheck_2965_ == 0 {
                            v___x_2957_ = v_v_2945_;
                            v_isShared_2958_ = v_isSharedCheck_2965_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2955_);
                            lean_inc(v_key_2954_);
                            lean_dec(v_v_2945_);
                            v___x_2957_ = lean_box(0);
                            v_isShared_2958_ = v_isSharedCheck_2965_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2966_ = lean_ctor_get(v_v_2945_, 0);
                        v_isSharedCheck_2976_ = (!lean_is_exclusive(v_v_2945_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2968_ = v_v_2945_;
                            v_isShared_2969_ = v_isSharedCheck_2976_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2966_);
                            lean_dec(v_v_2945_);
                            v___x_2968_ = lean_box(0);
                            v_isShared_2969_ = v_isSharedCheck_2976_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2977_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2977_, 0, v_x_2932_);
                        lean_ctor_set(v___x_2977_, 1, v_x_2933_);
                        v___y_2949_ = v___x_2977_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2950_ = lean_array_fset(v_xs_x27_2947_, v_j_2939_, v___y_2949_);
                lean_dec(v_j_2939_);
                if v_isShared_2944_ == 0 {
                    lean_ctor_set(v___x_2943_, 0, v___x_2950_);
                    v___x_2952_ = v___x_2943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
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
                    lean_del_object(v___x_2957_);
                    v___x_2960_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2954_,
                        v_val_2955_,
                        v_x_2932_,
                        v_x_2933_,
                    );
                    v___x_2961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2961_, 0, v___x_2960_);
                    v___y_2949_ = v___x_2961_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2955_);
                    lean_dec(v_key_2954_);
                    if v_isShared_2958_ == 0 {
                        lean_ctor_set(v___x_2957_, 1, v_x_2933_);
                        lean_ctor_set(v___x_2957_, 0, v_x_2932_);
                        v___x_2963_ = v___x_2957_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_x_2932_);
                        lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_x_2933_);
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
                    lean_ctor_set(v___x_2968_, 0, v___x_2972_);
                    v___x_2974_ = v___x_2968_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
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
                    v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_ks_2980_);
                    lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_vs_2981_);
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
                    v___x_2998_ = lean_unsigned_to_nat(4);
                    v___x_2999_ = lean_nat_dec_lt(v___x_2997_, v___x_2998_);
                    lean_dec(v___x_2997_);
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
                    v_ks_2990_ = lean_ctor_get(v_newNode_2987_, 0);
                    lean_inc_ref(v_ks_2990_);
                    v_vs_2991_ = lean_ctor_get(v_newNode_2987_, 1);
                    lean_inc_ref(v_vs_2991_);
                    lean_dec_ref(v_newNode_2987_);
                    v___x_2992_ = lean_unsigned_to_nat(0);
                    v___x_2993_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___closed__2);
                    v___x_2994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_x_2931_, v_ks_2990_, v_vs_2991_, v___x_2992_, v___x_2993_);
                    lean_dec_ref(v_vs_2991_);
                    lean_dec_ref(v_ks_2990_);
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
    mut v_keys_3003_: *mut LeanObject,
    mut v_vals_3004_: *mut LeanObject,
    mut v_i_3005_: *mut LeanObject,
    mut v_entries_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v_k_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: u64 = 0;
    let mut v_h_3012_: usize = 0;
    let mut v___x_3013_: usize = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: usize = 0;
    let mut v___x_3017_: usize = 0;
    let mut v_h_3018_: usize = 0;
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = lean_array_get_size(v_keys_3003_);
                v___x_3008_ = lean_nat_dec_lt(v_i_3005_, v___x_3007_);
                if v___x_3008_ == 0 {
                    lean_dec(v_i_3005_);
                    return v_entries_3006_;
                } else {
                    v_k_3009_ = lean_array_fget_borrowed(v_keys_3003_, v_i_3005_);
                    v_v_3010_ = lean_array_fget_borrowed(v_vals_3004_, v_i_3005_);
                    v___x_3011_ = l_Lean_instHashableMVarId_hash(v_k_3009_);
                    v_h_3012_ = lean_uint64_to_usize(v___x_3011_);
                    v___x_3013_ = 5usize;
                    v___x_3014_ = lean_unsigned_to_nat(1);
                    v___x_3015_ = 1usize;
                    v___x_3016_ = lean_usize_sub(v_depth_3002_, v___x_3015_);
                    v___x_3017_ = lean_usize_mul(v___x_3013_, v___x_3016_);
                    v_h_3018_ = lean_usize_shift_right(v_h_3012_, v___x_3017_);
                    v___x_3019_ = lean_nat_add(v_i_3005_, v___x_3014_);
                    lean_dec(v_i_3005_);
                    lean_inc(v_v_3010_);
                    lean_inc(v_k_3009_);
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
    mut v_depth_3022_: *mut LeanObject,
    mut v_keys_3023_: *mut LeanObject,
    mut v_vals_3024_: *mut LeanObject,
    mut v_i_3025_: *mut LeanObject,
    mut v_entries_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3027_: usize = 0;
    let mut v_res_3028_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3027_ = lean_unbox_usize(v_depth_3022_);
    lean_dec(v_depth_3022_);
    v_res_3028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_boxed_3027_, v_keys_3023_, v_vals_3024_, v_i_3025_, v_entries_3026_);
    lean_dec_ref(v_vals_3024_);
    lean_dec_ref(v_keys_3023_);
    return v_res_3028_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_x_3029_: *mut LeanObject,
    mut v_x_3030_: *mut LeanObject,
    mut v_x_3031_: *mut LeanObject,
    mut v_x_3032_: *mut LeanObject,
    mut v_x_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_24196__boxed_3034_: usize = 0;
    let mut v_x_24197__boxed_3035_: usize = 0;
    let mut v_res_3036_: *mut LeanObject = core::ptr::null_mut();
    v_x_24196__boxed_3034_ = lean_unbox_usize(v_x_3030_);
    lean_dec(v_x_3030_);
    v_x_24197__boxed_3035_ = lean_unbox_usize(v_x_3031_);
    lean_dec(v_x_3031_);
    v_res_3036_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3029_, v_x_24196__boxed_3034_, v_x_24197__boxed_3035_, v_x_3032_, v_x_3033_);
    return v_res_3036_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(
    mut v_x_3037_: *mut LeanObject,
    mut v_x_3038_: *mut LeanObject,
    mut v_x_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3040_: u64 = 0;
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    v___x_3040_ = l_Lean_instHashableMVarId_hash(v_x_3038_);
    v___x_3041_ = lean_uint64_to_usize(v___x_3040_);
    v___x_3042_ = 1usize;
    v___x_3043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3037_, v___x_3041_, v___x_3042_, v_x_3038_, v_x_3039_);
    return v___x_3043_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
    mut v_mvarId_3044_: *mut LeanObject,
    mut v_val_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v_depth_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_isSharedCheck_3081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3048_ = lean_st_ref_take(v___y_3046_);
                v_mctx_3049_ = lean_ctor_get(v___x_3048_, 0);
                v_cache_3050_ = lean_ctor_get(v___x_3048_, 1);
                v_zetaDeltaFVarIds_3051_ = lean_ctor_get(v___x_3048_, 2);
                v_postponed_3052_ = lean_ctor_get(v___x_3048_, 3);
                v_diag_3053_ = lean_ctor_get(v___x_3048_, 4);
                v_isSharedCheck_3081_ = (!lean_is_exclusive(v___x_3048_)) as u8;
                if v_isSharedCheck_3081_ == 0 {
                    v___x_3055_ = v___x_3048_;
                    v_isShared_3056_ = v_isSharedCheck_3081_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3053_);
                    lean_inc(v_postponed_3052_);
                    lean_inc(v_zetaDeltaFVarIds_3051_);
                    lean_inc(v_cache_3050_);
                    lean_inc(v_mctx_3049_);
                    lean_dec(v___x_3048_);
                    v___x_3055_ = lean_box(0);
                    v_isShared_3056_ = v_isSharedCheck_3081_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3057_ = lean_ctor_get(v_mctx_3049_, 0);
                v_levelAssignDepth_3058_ = lean_ctor_get(v_mctx_3049_, 1);
                v_lmvarCounter_3059_ = lean_ctor_get(v_mctx_3049_, 2);
                v_mvarCounter_3060_ = lean_ctor_get(v_mctx_3049_, 3);
                v_lDecls_3061_ = lean_ctor_get(v_mctx_3049_, 4);
                v_decls_3062_ = lean_ctor_get(v_mctx_3049_, 5);
                v_userNames_3063_ = lean_ctor_get(v_mctx_3049_, 6);
                v_lAssignment_3064_ = lean_ctor_get(v_mctx_3049_, 7);
                v_eAssignment_3065_ = lean_ctor_get(v_mctx_3049_, 8);
                v_dAssignment_3066_ = lean_ctor_get(v_mctx_3049_, 9);
                v_isSharedCheck_3080_ = (!lean_is_exclusive(v_mctx_3049_)) as u8;
                if v_isSharedCheck_3080_ == 0 {
                    v___x_3068_ = v_mctx_3049_;
                    v_isShared_3069_ = v_isSharedCheck_3080_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3066_);
                    lean_inc(v_eAssignment_3065_);
                    lean_inc(v_lAssignment_3064_);
                    lean_inc(v_userNames_3063_);
                    lean_inc(v_decls_3062_);
                    lean_inc(v_lDecls_3061_);
                    lean_inc(v_mvarCounter_3060_);
                    lean_inc(v_lmvarCounter_3059_);
                    lean_inc(v_levelAssignDepth_3058_);
                    lean_inc(v_depth_3057_);
                    lean_dec(v_mctx_3049_);
                    v___x_3068_ = lean_box(0);
                    v_isShared_3069_ = v_isSharedCheck_3080_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3070_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_eAssignment_3065_, v_mvarId_3044_, v_val_3045_);
                if v_isShared_3069_ == 0 {
                    lean_ctor_set(v___x_3068_, 8, v___x_3070_);
                    v___x_3072_ = v___x_3068_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_depth_3057_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_levelAssignDepth_3058_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_lmvarCounter_3059_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_mvarCounter_3060_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_lDecls_3061_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 5, v_decls_3062_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_userNames_3063_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_lAssignment_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 8, v___x_3070_);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 9, v_dAssignment_3066_);
                    v___x_3072_ = v_reuseFailAlloc_3079_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3056_ == 0 {
                    lean_ctor_set(v___x_3055_, 0, v___x_3072_);
                    v___x_3074_ = v___x_3055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3072_);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_cache_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_zetaDeltaFVarIds_3051_);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 3, v_postponed_3052_);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 4, v_diag_3053_);
                    v___x_3074_ = v_reuseFailAlloc_3078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3075_ = lean_st_ref_set(v___y_3046_, v___x_3074_);
                v___x_3076_ = lean_box(0);
                v___x_3077_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3077_, 0, v___x_3076_);
                return v___x_3077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg___boxed(
    mut v_mvarId_3082_: *mut LeanObject,
    mut v_val_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3086_: *mut LeanObject = core::ptr::null_mut();
    v_res_3086_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
            v_mvarId_3082_,
            v_val_3083_,
            v___y_3084_,
        );
    lean_dec(v___y_3084_);
    return v_res_3086_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1() -> *mut LeanObject {
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    v___x_3089_ = l_Lean_NameSet_empty;
    v___x_3090_ = l_Lean_Elab_Tactic_renameInaccessibles___closed__0;
    v___x_3091_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3091_, 0, v___x_3090_);
    lean_ctor_set(v___x_3091_, 1, v___x_3089_);
    return v___x_3091_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__3() -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_Elab_Tactic_renameInaccessibles___closed__2;
    v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn l_Lean_Elab_Tactic_renameInaccessibles(
    mut v_mvarId_3097_: *mut LeanObject,
    mut v_hs_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
    mut v_a_3100_: *mut LeanObject,
    mut v_a_3101_: *mut LeanObject,
    mut v_a_3102_: *mut LeanObject,
    mut v_a_3103_: *mut LeanObject,
    mut v_a_3104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3155_: usize = 0;
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_unused_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_a_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v_a_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_reuseFailAlloc_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut v_unused_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_a_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3106_ = lean_array_get_size(v_hs_3098_);
                v___x_3107_ = lean_unsigned_to_nat(0);
                v___x_3108_ = lean_nat_dec_eq(v___x_3106_, v___x_3107_);
                if v___x_3108_ == 0 {
                    lean_inc(v_mvarId_3097_);
                    v___x_3109_ = l_Lean_MVarId_getDecl(
                        v_mvarId_3097_,
                        v_a_3101_,
                        v_a_3102_,
                        v_a_3103_,
                        v_a_3104_,
                    );
                    if lean_obj_tag(v___x_3109_) == 0 {
                        v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
                        v_isSharedCheck_3212_ = (!lean_is_exclusive(v___x_3109_)) as u8;
                        if v_isSharedCheck_3212_ == 0 {
                            v___x_3112_ = v___x_3109_;
                            v_isShared_3113_ = v_isSharedCheck_3212_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3110_);
                            lean_dec(v___x_3109_);
                            v___x_3112_ = lean_box(0);
                            v_isShared_3113_ = v_isSharedCheck_3212_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_hs_3098_);
                        lean_dec(v_mvarId_3097_);
                        v_a_3213_ = lean_ctor_get(v___x_3109_, 0);
                        v_isSharedCheck_3220_ = (!lean_is_exclusive(v___x_3109_)) as u8;
                        if v_isSharedCheck_3220_ == 0 {
                            v___x_3215_ = v___x_3109_;
                            v_isShared_3216_ = v_isSharedCheck_3220_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3213_);
                            lean_dec(v___x_3109_);
                            v___x_3215_ = lean_box(0);
                            v_isShared_3216_ = v_isSharedCheck_3220_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_hs_3098_);
                    v___x_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3221_, 0, v_mvarId_3097_);
                    return v___x_3221_;
                }
            }
            1 => {
                v___x_3114_ = lean_box(0);
                v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5___closed__0;
                v_sz_3116_ = lean_array_size(v_hs_3098_);
                v___x_3117_ = 0usize;
                v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_renameInaccessibles_spec__5(v_hs_3098_, v_sz_3116_, v___x_3117_, v___x_3115_);
                v_fst_3119_ = lean_ctor_get(v___x_3118_, 0);
                v_isSharedCheck_3210_ = (!lean_is_exclusive(v___x_3118_)) as u8;
                if v_isSharedCheck_3210_ == 0 {
                    v_unused_3211_ = lean_ctor_get(v___x_3118_, 1);
                    lean_dec(v_unused_3211_);
                    v___x_3121_ = v___x_3118_;
                    v_isShared_3122_ = v_isSharedCheck_3210_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_3119_);
                    lean_dec(v___x_3118_);
                    v___x_3121_ = lean_box(0);
                    v_isShared_3122_ = v_isSharedCheck_3210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_fst_3119_) == 0 {
                    lean_del_object(v___x_3121_);
                    lean_dec(v_a_3110_);
                    lean_dec_ref(v_hs_3098_);
                    if v_isShared_3113_ == 0 {
                        lean_ctor_set(v___x_3112_, 0, v_mvarId_3097_);
                        v___x_3124_ = v___x_3112_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_mvarId_3097_);
                        v___x_3124_ = v_reuseFailAlloc_3125_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_3126_ = lean_ctor_get(v_fst_3119_, 0);
                    lean_inc(v_val_3126_);
                    lean_dec_ref_known(v_fst_3119_, 1);
                    if lean_obj_tag(v_val_3126_) == 1 {
                        lean_del_object(v___x_3112_);
                        v_val_3127_ = lean_ctor_get(v_val_3126_, 0);
                        lean_inc(v_val_3127_);
                        lean_dec_ref_known(v_val_3126_, 1);
                        v_userName_3128_ = lean_ctor_get(v_a_3110_, 0);
                        lean_inc(v_userName_3128_);
                        v_lctx_3129_ = lean_ctor_get(v_a_3110_, 1);
                        lean_inc_ref_n(v_lctx_3129_, 2);
                        v_type_3130_ = lean_ctor_get(v_a_3110_, 2);
                        lean_inc_ref(v_type_3130_);
                        v_localInstances_3131_ = lean_ctor_get(v_a_3110_, 4);
                        lean_inc_ref(v_localInstances_3131_);
                        lean_dec(v_a_3110_);
                        v___x_3132_ = lean_local_ctx_num_indices(v_lctx_3129_);
                        v___x_3133_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_renameInaccessibles___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_renameInaccessibles___closed__1,
                        );
                        if v_isShared_3122_ == 0 {
                            lean_ctor_set(v___x_3121_, 1, v___x_3133_);
                            lean_ctor_set(v___x_3121_, 0, v_hs_3098_);
                            v___x_3135_ = v___x_3121_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_hs_3098_);
                            lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3133_);
                            v___x_3135_ = v_reuseFailAlloc_3206_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3126_);
                        lean_del_object(v___x_3121_);
                        lean_dec(v_a_3110_);
                        lean_dec_ref(v_hs_3098_);
                        if v_isShared_3113_ == 0 {
                            lean_ctor_set(v___x_3112_, 0, v_mvarId_3097_);
                            v___x_3208_ = v___x_3112_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_mvarId_3097_);
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
                v___x_3136_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3136_, 0, v_lctx_3129_);
                lean_ctor_set(v___x_3136_, 1, v___x_3135_);
                v___x_3137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v___x_3132_, v___x_3132_, v_val_3127_, v___x_3107_, v___x_3136_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
                lean_dec(v_val_3127_);
                lean_dec(v___x_3132_);
                if lean_obj_tag(v___x_3137_) == 0 {
                    v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
                    lean_inc(v_a_3138_);
                    lean_dec_ref_known(v___x_3137_, 1);
                    v_snd_3139_ = lean_ctor_get(v_a_3138_, 1);
                    lean_inc(v_snd_3139_);
                    v_snd_3140_ = lean_ctor_get(v_snd_3139_, 1);
                    lean_inc(v_snd_3140_);
                    v_fst_3141_ = lean_ctor_get(v_a_3138_, 0);
                    lean_inc(v_fst_3141_);
                    lean_dec(v_a_3138_);
                    v_fst_3142_ = lean_ctor_get(v_snd_3139_, 0);
                    lean_inc(v_fst_3142_);
                    lean_dec(v_snd_3139_);
                    v_fst_3143_ = lean_ctor_get(v_snd_3140_, 0);
                    lean_inc(v_fst_3143_);
                    lean_dec(v_snd_3140_);
                    v___x_3186_ = lean_array_get_size(v_fst_3142_);
                    lean_dec(v_fst_3142_);
                    v___x_3187_ = lean_nat_dec_eq(v___x_3186_, v___x_3107_);
                    if v___x_3187_ == 0 {
                        v___x_3188_ = lean_obj_once(
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
                        if lean_obj_tag(v___x_3189_) == 0 {
                            lean_dec_ref_known(v___x_3189_, 1);
                            v___y_3145_ = v_a_3099_;
                            v___y_3146_ = v_a_3100_;
                            v___y_3147_ = v_a_3101_;
                            v___y_3148_ = v_a_3102_;
                            v___y_3149_ = v_a_3103_;
                            v___y_3150_ = v_a_3104_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_fst_3143_);
                            lean_dec(v_fst_3141_);
                            lean_dec_ref(v_localInstances_3131_);
                            lean_dec_ref(v_type_3130_);
                            lean_dec(v_userName_3128_);
                            lean_dec(v_mvarId_3097_);
                            v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
                            v_isSharedCheck_3197_ = (!lean_is_exclusive(v___x_3189_)) as u8;
                            if v_isSharedCheck_3197_ == 0 {
                                v___x_3192_ = v___x_3189_;
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3190_);
                                lean_dec(v___x_3189_);
                                v___x_3192_ = lean_box(0);
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
                    lean_dec_ref(v_localInstances_3131_);
                    lean_dec_ref(v_type_3130_);
                    lean_dec(v_userName_3128_);
                    lean_dec(v_mvarId_3097_);
                    v_a_3198_ = lean_ctor_get(v___x_3137_, 0);
                    v_isSharedCheck_3205_ = (!lean_is_exclusive(v___x_3137_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v___x_3200_ = v___x_3137_;
                        v_isShared_3201_ = v_isSharedCheck_3205_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3198_);
                        lean_dec(v___x_3137_);
                        v___x_3200_ = lean_box(0);
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
                if lean_obj_tag(v___x_3152_) == 0 {
                    v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
                    lean_inc(v_a_3153_);
                    lean_dec_ref_known(v___x_3152_, 1);
                    v___x_3154_ = l_Lean_Expr_mvarId_x21(v_a_3153_);
                    v_sz_3155_ = lean_array_size(v_fst_3143_);
                    v___x_3156_ = lean_box_usize(v_sz_3155_);
                    v___x_3157_ = l_Lean_Elab_Tactic_renameInaccessibles___boxed__const__1;
                    v___f_3158_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_renameInaccessibles___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    lean_closure_set(v___f_3158_, 0, v_fst_3143_);
                    lean_closure_set(v___f_3158_, 1, v___x_3156_);
                    lean_closure_set(v___f_3158_, 2, v___x_3157_);
                    lean_closure_set(v___f_3158_, 3, v___x_3114_);
                    lean_inc(v___x_3154_);
                    v___x_3159_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__1___boxed as *mut core::ffi::c_void, 10, 3);
                    lean_closure_set(v___x_3159_, 0, lean_box(0));
                    lean_closure_set(v___x_3159_, 1, v___x_3154_);
                    lean_closure_set(v___x_3159_, 2, v___f_3158_);
                    v___x_3160_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v___x_3159_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
                    if lean_obj_tag(v___x_3160_) == 0 {
                        lean_dec_ref_known(v___x_3160_, 1);
                        v___x_3161_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(v_mvarId_3097_, v_a_3153_, v___y_3148_);
                        v_isSharedCheck_3168_ = (!lean_is_exclusive(v___x_3161_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v_unused_3169_ = lean_ctor_get(v___x_3161_, 0);
                            lean_dec(v_unused_3169_);
                            v___x_3163_ = v___x_3161_;
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_3161_);
                            v___x_3163_ = lean_box(0);
                            v_isShared_3164_ = v_isSharedCheck_3168_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3154_);
                        lean_dec(v_a_3153_);
                        lean_dec(v_mvarId_3097_);
                        v_a_3170_ = lean_ctor_get(v___x_3160_, 0);
                        v_isSharedCheck_3177_ = (!lean_is_exclusive(v___x_3160_)) as u8;
                        if v_isSharedCheck_3177_ == 0 {
                            v___x_3172_ = v___x_3160_;
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3170_);
                            lean_dec(v___x_3160_);
                            v___x_3172_ = lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_3143_);
                    lean_dec(v_mvarId_3097_);
                    v_a_3178_ = lean_ctor_get(v___x_3152_, 0);
                    v_isSharedCheck_3185_ = (!lean_is_exclusive(v___x_3152_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3180_ = v___x_3152_;
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3178_);
                        lean_dec(v___x_3152_);
                        v___x_3180_ = lean_box(0);
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3164_ == 0 {
                    lean_ctor_set(v___x_3163_, 0, v___x_3154_);
                    v___x_3166_ = v___x_3163_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3154_);
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
                    v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
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
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
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
                    v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
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
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
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
                    v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
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
    mut v_mvarId_3222_: *mut LeanObject,
    mut v_hs_3223_: *mut LeanObject,
    mut v_a_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3231_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3229_);
    lean_dec_ref(v_a_3228_);
    lean_dec(v_a_3227_);
    lean_dec_ref(v_a_3226_);
    lean_dec(v_a_3225_);
    lean_dec_ref(v_a_3224_);
    return v_res_3231_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2(
    mut v_00_u03b1_3232_: *mut LeanObject,
    mut v_x_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___redArg(v_x_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
    return v___x_3241_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2___boxed(
    mut v_00_u03b1_3242_: *mut LeanObject,
    mut v_x_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3251_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3249_);
    lean_dec_ref(v___y_3248_);
    lean_dec(v___y_3247_);
    lean_dec_ref(v___y_3246_);
    lean_dec(v___y_3245_);
    lean_dec_ref(v___y_3244_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3(
    mut v_mvarId_3252_: *mut LeanObject,
    mut v_val_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
    mut v___y_3255_: *mut LeanObject,
    mut v___y_3256_: *mut LeanObject,
    mut v___y_3257_: *mut LeanObject,
    mut v___y_3258_: *mut LeanObject,
    mut v___y_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    v___x_3261_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___redArg(
            v_mvarId_3252_,
            v_val_3253_,
            v___y_3257_,
        );
    return v___x_3261_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3___boxed(
    mut v_mvarId_3262_: *mut LeanObject,
    mut v_val_3263_: *mut LeanObject,
    mut v___y_3264_: *mut LeanObject,
    mut v___y_3265_: *mut LeanObject,
    mut v___y_3266_: *mut LeanObject,
    mut v___y_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3271_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3269_);
    lean_dec_ref(v___y_3268_);
    lean_dec(v___y_3267_);
    lean_dec_ref(v___y_3266_);
    lean_dec(v___y_3265_);
    lean_dec_ref(v___y_3264_);
    return v_res_3271_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6(
    mut v_upperBound_3272_: *mut LeanObject,
    mut v___x_3273_: *mut LeanObject,
    mut v_val_3274_: *mut LeanObject,
    mut v_inst_3275_: *mut LeanObject,
    mut v_R_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_b_3278_: *mut LeanObject,
    mut v_c_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
    mut v___y_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___x_3287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___redArg(v_upperBound_3272_, v___x_3273_, v_val_3274_, v_a_3277_, v_b_3278_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
    return v___x_3287_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_renameInaccessibles_spec__6___boxed(
    mut v_upperBound_3288_: *mut LeanObject,
    mut v___x_3289_: *mut LeanObject,
    mut v_val_3290_: *mut LeanObject,
    mut v_inst_3291_: *mut LeanObject,
    mut v_R_3292_: *mut LeanObject,
    mut v_a_3293_: *mut LeanObject,
    mut v_b_3294_: *mut LeanObject,
    mut v_c_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3303_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3301_);
    lean_dec_ref(v___y_3300_);
    lean_dec(v___y_3299_);
    lean_dec_ref(v___y_3298_);
    lean_dec(v___y_3297_);
    lean_dec_ref(v___y_3296_);
    lean_dec_ref(v_val_3290_);
    lean_dec(v___x_3289_);
    lean_dec(v_upperBound_3288_);
    return v_res_3303_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___redArg(v___y_3307_, v___y_3308_, v___y_3309_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3___boxed(
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
    mut v___y_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3319_: *mut LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__2_spec__3(v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
    lean_dec(v___y_3317_);
    lean_dec_ref(v___y_3316_);
    lean_dec(v___y_3315_);
    lean_dec_ref(v___y_3314_);
    lean_dec(v___y_3313_);
    lean_dec_ref(v___y_3312_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    v___x_3327_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___redArg(v___y_3325_);
    return v___x_3327_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5___boxed(
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3335_: *mut LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3_spec__5(v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    lean_dec(v___y_3333_);
    lean_dec_ref(v___y_3332_);
    lean_dec(v___y_3331_);
    lean_dec_ref(v___y_3330_);
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    return v_res_3335_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(
    mut v_00_u03b1_3336_: *mut LeanObject,
    mut v_x_3337_: *mut LeanObject,
    mut v_ctx_x3f_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3346_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___redArg(v_x_3337_, v_ctx_x3f_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
    return v___x_3346_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3___boxed(
    mut v_00_u03b1_3347_: *mut LeanObject,
    mut v_x_3348_: *mut LeanObject,
    mut v_ctx_x3f_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_renameInaccessibles_spec__2_spec__3(v_00_u03b1_3347_, v_x_3348_, v_ctx_x3f_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
    lean_dec(v___y_3355_);
    lean_dec_ref(v___y_3354_);
    lean_dec(v___y_3353_);
    lean_dec_ref(v___y_3352_);
    lean_dec(v___y_3351_);
    lean_dec_ref(v___y_3350_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5(
    mut v_00_u03b2_3358_: *mut LeanObject,
    mut v_x_3359_: *mut LeanObject,
    mut v_x_3360_: *mut LeanObject,
    mut v_x_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    v___x_3362_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5___redArg(v_x_3359_, v_x_3360_, v_x_3361_);
    return v___x_3362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(
    mut v_00_u03b2_3363_: *mut LeanObject,
    mut v_x_3364_: *mut LeanObject,
    mut v_x_3365_: usize,
    mut v_x_3366_: usize,
    mut v_x_3367_: *mut LeanObject,
    mut v_x_3368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    v___x_3369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___redArg(v_x_3364_, v_x_3365_, v_x_3366_, v_x_3367_, v_x_3368_);
    return v___x_3369_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03b2_3370_: *mut LeanObject,
    mut v_x_3371_: *mut LeanObject,
    mut v_x_3372_: *mut LeanObject,
    mut v_x_3373_: *mut LeanObject,
    mut v_x_3374_: *mut LeanObject,
    mut v_x_3375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_24820__boxed_3376_: usize = 0;
    let mut v_x_24821__boxed_3377_: usize = 0;
    let mut v_res_3378_: *mut LeanObject = core::ptr::null_mut();
    v_x_24820__boxed_3376_ = lean_unbox_usize(v_x_3372_);
    lean_dec(v_x_3372_);
    v_x_24821__boxed_3377_ = lean_unbox_usize(v_x_3373_);
    lean_dec(v_x_3373_);
    v_res_3378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9(v_00_u03b2_3370_, v_x_3371_, v_x_24820__boxed_3376_, v_x_24821__boxed_3377_, v_x_3374_, v_x_3375_);
    return v_res_3378_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(
    mut v_ref_3379_: *mut LeanObject,
    mut v_msgData_3380_: *mut LeanObject,
    mut v_severity_3381_: u8,
    mut v_isSilent_3382_: u8,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___redArg(v_ref_3379_, v_msgData_3380_, v_severity_3381_, v_isSilent_3382_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    return v___x_3390_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12___boxed(
    mut v_ref_3391_: *mut LeanObject,
    mut v_msgData_3392_: *mut LeanObject,
    mut v_severity_3393_: *mut LeanObject,
    mut v_isSilent_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3402_: u8 = 0;
    let mut v_isSilent_boxed_3403_: u8 = 0;
    let mut v_res_3404_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3402_ = (lean_unbox(v_severity_3393_) as u8);
    v_isSilent_boxed_3403_ = (lean_unbox(v_isSilent_3394_) as u8);
    v_res_3404_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_renameInaccessibles_spec__4_spec__7_spec__12(v_ref_3391_, v_msgData_3392_, v_severity_boxed_3402_, v_isSilent_boxed_3403_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
    lean_dec(v___y_3400_);
    lean_dec_ref(v___y_3399_);
    lean_dec(v___y_3398_);
    lean_dec_ref(v___y_3397_);
    lean_dec(v___y_3396_);
    lean_dec_ref(v___y_3395_);
    lean_dec(v_ref_3391_);
    return v_res_3404_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15(
    mut v_00_u03b2_3405_: *mut LeanObject,
    mut v_n_3406_: *mut LeanObject,
    mut v_k_3407_: *mut LeanObject,
    mut v_v_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15___redArg(v_n_3406_, v_k_3407_, v_v_3408_);
    return v___x_3409_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(
    mut v_00_u03b2_3410_: *mut LeanObject,
    mut v_depth_3411_: usize,
    mut v_keys_3412_: *mut LeanObject,
    mut v_vals_3413_: *mut LeanObject,
    mut v_heq_3414_: *mut LeanObject,
    mut v_i_3415_: *mut LeanObject,
    mut v_entries_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3417_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___redArg(v_depth_3411_, v_keys_3412_, v_vals_3413_, v_i_3415_, v_entries_3416_);
    return v___x_3417_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16___boxed(
    mut v_00_u03b2_3418_: *mut LeanObject,
    mut v_depth_3419_: *mut LeanObject,
    mut v_keys_3420_: *mut LeanObject,
    mut v_vals_3421_: *mut LeanObject,
    mut v_heq_3422_: *mut LeanObject,
    mut v_i_3423_: *mut LeanObject,
    mut v_entries_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3425_: usize = 0;
    let mut v_res_3426_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3425_ = lean_unbox_usize(v_depth_3419_);
    lean_dec(v_depth_3419_);
    v_res_3426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__16(v_00_u03b2_3418_, v_depth_boxed_3425_, v_keys_3420_, v_vals_3421_, v_heq_3422_, v_i_3423_, v_entries_3424_);
    lean_dec_ref(v_vals_3421_);
    lean_dec_ref(v_keys_3420_);
    return v_res_3426_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18(
    mut v_00_u03b2_3427_: *mut LeanObject,
    mut v_x_3428_: *mut LeanObject,
    mut v_x_3429_: *mut LeanObject,
    mut v_x_3430_: *mut LeanObject,
    mut v_x_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    v___x_3432_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_renameInaccessibles_spec__3_spec__5_spec__9_spec__15_spec__18___redArg(v_x_3428_, v_x_3429_, v_x_3430_, v_x_3431_);
    return v___x_3432_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Binders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
}
