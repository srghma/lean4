// Lean compiler output
// Module: Lean.Linter.Extra.UnnecessarySeqFocus
// Imports: Lean.Elab.Command Lean.Linter.Basic
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Ord::Basic::{
    l_instOrdInt___lam__0___boxed, l_instOrdNat___lam__0___boxed, l_lexOrd___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::System::ST::{l_instMonadST, l_runST___redArg};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Types::l_Lean_Elab_instInhabitedInfoTree_default;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValueExtra, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instBEqRange_beq,
    l_Lean_Syntax_instBEqRange_beq___boxed, l_Lean_Syntax_instHashableRange_hash,
    l_Lean_Syntax_instHashableRange_hash___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insert___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_neg, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 83, 101, 113, 70, 111, 99, 117, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,8383467597245298465 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,9979626473568214133 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 32, 60, 59, 62, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,8412578185445384546 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,9890441027862740329 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,15829786020280644061 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 97, 99, 116, 105, 99, 78, 101, 120, 116, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__2_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,4774833825831523674 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,14131640301685195369 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 110, 121, 71, 111, 97, 108, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2355218674864034728 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 101, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,3714280620155270360 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 39, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,7640173075534255494 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 111, 110, 118, 78, 101, 120, 116, 95, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__13_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,3719486818457681805 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__4_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,1113262671135127376 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,17733550178357422433 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,11752510286238259185 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__10_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2260385614914559383 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__19_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8933670559188175167 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__21_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,9818594054304805218 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 104, 111, 119, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__23_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,4563519173115679639 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 83, 116, 111, 112, 95, 0]};
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__25_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,7782951904519764922 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value: LeanArrayObject<14> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*14) as u16, other: 0, tag: 246 }, m_size: 14, m_capacity: 14, m_data: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__11_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__14_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__15_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__16_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__17_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__18_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__20_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__22_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__24_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__26_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value)
        as *mut LeanObject;
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__0_value
            ) as *mut LeanObject,
            12695378809397736991 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [99, 111, 110, 118, 95, 60, 59, 62, 95, 0],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value)
        as *mut LeanObject;
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__0_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__1_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__12_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2__value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__2_value
            ) as *mut LeanObject,
            2841688605323704715 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_instBEqRange_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_instHashableRange_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10_value
) as *mut LeanObject;
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [85, 115, 101, 100, 32, 96, 116, 97, 99, 49, 32, 60, 59, 62, 32, 116, 97, 99, 50, 96, 32, 119, 104, 101, 114, 101, 32, 96, 40, 116, 97, 99, 49, 59, 32, 116, 97, 99, 50, 41, 96, 32, 119, 111, 117, 108, 100, 32, 115, 117, 102, 102, 105, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instOrdNat___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instOrdInt___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        85, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 83, 101, 113, 70, 111, 99, 117, 115, 0,
    ],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 83, 101, 113, 70, 111, 99, 117, 115,
        76, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value
) as *mut LeanObject;
static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__2_value) as *mut LeanObject,11062029876199923315 as *mut LeanObject] };
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__3_value) as *mut LeanObject,10367355181368324187 as *mut LeanObject] };
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value
) as *mut LeanObject;
pub static mut l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___closed__5_value
)
    as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(
    mut v_name_1881_: *mut LeanObject,
    mut v_decl_1882_: *mut LeanObject,
    mut v_ref_1883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: u8 = 0;
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1885_ = lean_ctor_get(v_decl_1882_, 0);
                v_descr_1886_ = lean_ctor_get(v_decl_1882_, 1);
                v_deprecation_x3f_1887_ = lean_ctor_get(v_decl_1882_, 2);
                v___x_1888_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1889_ = (lean_unbox(v_defValue_1885_) as u8);
                lean_ctor_set_uint8(v___x_1888_, 0 as u32, v___x_1889_);
                lean_inc(v_deprecation_x3f_1887_);
                lean_inc_ref(v_descr_1886_);
                lean_inc_n(v_name_1881_, 2);
                v___x_1890_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1890_, 0, v_name_1881_);
                lean_ctor_set(v___x_1890_, 1, v_ref_1883_);
                lean_ctor_set(v___x_1890_, 2, v___x_1888_);
                lean_ctor_set(v___x_1890_, 3, v_descr_1886_);
                lean_ctor_set(v___x_1890_, 4, v_deprecation_x3f_1887_);
                v___x_1891_ = lean_register_option(v_name_1881_, v___x_1890_);
                if lean_obj_tag(v___x_1891_) == 0 {
                    v_isSharedCheck_1899_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                    if v_isSharedCheck_1899_ == 0 {
                        v_unused_1900_ = lean_ctor_get(v___x_1891_, 0);
                        lean_dec(v_unused_1900_);
                        v___x_1893_ = v___x_1891_;
                        v_isShared_1894_ = v_isSharedCheck_1899_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1891_);
                        v___x_1893_ = lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1899_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1881_);
                    v_a_1901_ = lean_ctor_get(v___x_1891_, 0);
                    v_isSharedCheck_1908_ = (!lean_is_exclusive(v___x_1891_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v___x_1903_ = v___x_1891_;
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1901_);
                        lean_dec(v___x_1891_);
                        v___x_1903_ = lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1908_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1885_);
                v___x_1895_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1895_, 0, v_name_1881_);
                lean_ctor_set(v___x_1895_, 1, v_defValue_1885_);
                if v_isShared_1894_ == 0 {
                    lean_ctor_set(v___x_1893_, 0, v___x_1895_);
                    v___x_1897_ = v___x_1893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
                    v___x_1897_ = v_reuseFailAlloc_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1897_;
            }
            3 => {
                if v_isShared_1904_ == 0 {
                    v___x_1906_ = v___x_1903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
                    v___x_1906_ = v_reuseFailAlloc_1907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1909_: *mut LeanObject,
    mut v_decl_1910_: *mut LeanObject,
    mut v_ref_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1913_: *mut LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(v_name_1909_, v_decl_1910_, v_ref_1911_);
    lean_dec_ref(v_decl_1910_);
    return v_res_1913_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    v___x_1938_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_;
    v___x_1939_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_;
    v___x_1940_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_;
    v___x_1941_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4__spec__0(v___x_1938_, v___x_1939_, v___x_1940_);
    return v___x_1941_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4____boxed(
    mut v_a_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1943_: *mut LeanObject = core::ptr::null_mut();
    v_res_1943_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_();
    return v_res_1943_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_NameSet_empty;
    v___x_1946_ = lean_st_mk_ref(v___x_1945_);
    v___x_1947_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1947_, 0, v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2____boxed(
    mut v_a_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_res_1949_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
    return v_res_1949_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind(
    mut v_k_1950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
    v___x_1953_ = lean_st_ref_take(v___x_1952_);
    v___x_1954_ = l_Lean_NameSet_insert(v___x_1953_, v_k_1950_);
    v___x_1955_ = lean_st_ref_set(v___x_1952_, v___x_1954_);
    v___x_1956_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1956_, 0, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind___boxed(
    mut v_k_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1959_: *mut LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKind(v_k_1957_);
    return v_res_1959_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(
    mut v_as_1960_: *mut LeanObject,
    mut v_i_1961_: usize,
    mut v_stop_1962_: usize,
    mut v_b_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: usize = 0;
    let mut v___x_1968_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1964_ = lean_usize_dec_eq(v_i_1961_, v_stop_1962_);
                if v___x_1964_ == 0 {
                    v___x_1965_ = lean_array_uget_borrowed(v_as_1960_, v_i_1961_);
                    lean_inc(v___x_1965_);
                    v___x_1966_ = l_Lean_NameSet_insert(v_b_1963_, v___x_1965_);
                    v___x_1967_ = 1usize;
                    v___x_1968_ = lean_usize_add(v_i_1961_, v___x_1967_);
                    v_i_1961_ = v___x_1968_;
                    v_b_1963_ = v___x_1966_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1963_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0___boxed(
    mut v_as_1970_: *mut LeanObject,
    mut v_i_1971_: *mut LeanObject,
    mut v_stop_1972_: *mut LeanObject,
    mut v_b_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1974_: usize = 0;
    let mut v_stop_boxed_1975_: usize = 0;
    let mut v_res_1976_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1974_ = lean_unbox_usize(v_i_1971_);
    lean_dec(v_i_1971_);
    v_stop_boxed_1975_ = lean_unbox_usize(v_stop_1972_);
    lean_dec(v_stop_1972_);
    v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_as_1970_, v_i_boxed_1974_, v_stop_boxed_1975_, v_b_1973_);
    lean_dec_ref(v_as_1970_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(
    mut v_ks_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: usize = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1979_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
                v___x_1980_ = lean_st_ref_take(v___x_1979_);
                v___x_1985_ = lean_unsigned_to_nat(0);
                v___x_1986_ = lean_array_get_size(v_ks_1977_);
                v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
                if v___x_1987_ == 0 {
                    v___y_1982_ = v___x_1980_;
                    state = 1;
                    continue;
                } else {
                    v___x_1988_ = lean_nat_dec_le(v___x_1986_, v___x_1986_);
                    if v___x_1988_ == 0 {
                        if v___x_1987_ == 0 {
                            v___y_1982_ = v___x_1980_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1989_ = 0usize;
                            v___x_1990_ = lean_usize_of_nat(v___x_1986_);
                            v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_1977_, v___x_1989_, v___x_1990_, v___x_1980_);
                            v___y_1982_ = v___x_1991_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1992_ = 0usize;
                        v___x_1993_ = lean_usize_of_nat(v___x_1986_);
                        v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds_spec__0(v_ks_1977_, v___x_1992_, v___x_1993_, v___x_1980_);
                        v___y_1982_ = v___x_1994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1983_ = lean_st_ref_set(v___x_1979_, v___y_1982_);
                v___x_1984_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1984_, 0, v___x_1983_);
                return v___x_1984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds___boxed(
    mut v_ks_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1997_: *mut LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v_ks_1995_);
    lean_dec_ref(v_ks_1995_);
    return v_res_1997_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn___closed__27_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_;
    v___x_2118_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_addBuiltinMultigoalKinds(v___x_2117_);
    return v___x_2118_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2____boxed(
    mut v_a_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2120_: *mut LeanObject = core::ptr::null_mut();
    v_res_2120_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
    return v_res_2120_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind(
    mut v_k_2121_: *mut LeanObject,
) -> u8 {
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: u8 = 0;
    v___x_2123_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
    v___x_2124_ = lean_st_ref_get(v___x_2123_);
    v___x_2125_ = l_Lean_NameSet_contains(v___x_2124_, v_k_2121_);
    lean_dec(v___x_2124_);
    return v___x_2125_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind___boxed(
    mut v_k_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2128_: u8 = 0;
    let mut v_r_2129_: *mut LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isMultigoalKind(v_k_2126_);
    lean_dec(v_k_2126_);
    v_r_2129_ = lean_box((v_res_2128_) as usize);
    return v_r_2129_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus(
    mut v_k_2143_: *mut LeanObject,
) -> u8 {
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: u8 = 0;
    v___x_2144_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1;
    v___x_2145_ = lean_name_eq(v_k_2143_, v___x_2144_);
    if v___x_2145_ == 0 {
        let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: u8 = 0;
        v___x_2146_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3;
        v___x_2147_ = lean_name_eq(v_k_2143_, v___x_2146_);
        return v___x_2147_;
    } else {
        return v___x_2145_;
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___boxed(
    mut v_k_2148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2149_: u8 = 0;
    let mut v_r_2150_: *mut LeanObject = core::ptr::null_mut();
    v_res_2149_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus(v_k_2148_);
    lean_dec(v_k_2148_);
    v_r_2150_ = lean_box((v_res_2149_) as usize);
    return v_r_2150_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2151_ = l_instMonadST(lean_box(0));
    return v___x_2151_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    v___x_2152_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__0,
    );
    v___x_2153_ = l_StateRefT_x27_instMonad___redArg(v___x_2152_);
    return v___x_2153_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed(
    mut v_x_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2158_: *mut LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(
        v_x_2154_,
        v___y_2155_,
        v___y_2156_,
    );
    lean_dec(v___y_2156_);
    return v_res_2158_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(
    mut v_stx_2161_: *mut LeanObject,
    mut v_a_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: usize = 0;
    let mut v___x_2176_: usize = 0;
    let mut v___x_749__overap_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: usize = 0;
    let mut v___x_754__overap_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2184_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: u8 = 0;
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1_once), _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__1);
                if lean_obj_tag(v_stx_2161_) == 1 {
                    v_kind_2165_ = lean_ctor_get(v_stx_2161_, 1);
                    v_args_2166_ = lean_ctor_get(v_stx_2161_, 2);
                    lean_inc_ref(v_args_2166_);
                    v___f_2167_ = lean_alloc_closure(
                        l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        0,
                    );
                    v___x_2194_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1;
                    v___x_2195_ = lean_name_eq(v_kind_2165_, v___x_2194_);
                    if v___x_2195_ == 0 {
                        v___x_2196_ =
                            l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3;
                        v___x_2197_ = lean_name_eq(v_kind_2165_, v___x_2196_);
                        v___y_2184_ = v___x_2197_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2184_ = v___x_2195_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_2161_);
                    v___x_2198_ = lean_box(0);
                    return v___x_2198_;
                }
            }
            1 => {
                v___x_2170_ = lean_unsigned_to_nat(0);
                v___x_2171_ = lean_array_get_size(v_args_2166_);
                v___x_2172_ = lean_box(0);
                v___x_2173_ = lean_nat_dec_lt(v___x_2170_, v___x_2171_);
                if v___x_2173_ == 0 {
                    lean_dec_ref(v___f_2167_);
                    lean_dec_ref(v_args_2166_);
                    return v___x_2172_;
                } else {
                    v___x_2174_ = lean_nat_dec_le(v___x_2171_, v___x_2171_);
                    if v___x_2174_ == 0 {
                        if v___x_2173_ == 0 {
                            lean_dec_ref(v___f_2167_);
                            lean_dec_ref(v_args_2166_);
                            return v___x_2172_;
                        } else {
                            v___x_2175_ = 0usize;
                            v___x_2176_ = lean_usize_of_nat(v___x_2171_);
                            v___x_749__overap_2177_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2164_,
                                    v___f_2167_,
                                    v_args_2166_,
                                    v___x_2175_,
                                    v___x_2176_,
                                    v___x_2172_,
                                );
                            lean_inc(v___y_2169_);
                            v___x_2178_ =
                                lean_apply_2(v___x_749__overap_2177_, v___y_2169_, lean_box(0));
                            return v___x_2178_;
                        }
                    } else {
                        v___x_2179_ = 0usize;
                        v___x_2180_ = lean_usize_of_nat(v___x_2171_);
                        v___x_754__overap_2181_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2164_,
                                v___f_2167_,
                                v_args_2166_,
                                v___x_2179_,
                                v___x_2180_,
                                v___x_2172_,
                            );
                        lean_inc(v___y_2169_);
                        v___x_2182_ =
                            lean_apply_2(v___x_754__overap_2181_, v___y_2169_, lean_box(0));
                        return v___x_2182_;
                    }
                }
            }
            2 => {
                if v___y_2184_ == 0 {
                    lean_dec_ref_known(v_stx_2161_, 3);
                    v___y_2169_ = v_a_2162_;
                    state = 1;
                    continue;
                } else {
                    v___x_2185_ = l_Lean_Syntax_getRange_x3f(v_stx_2161_, v___y_2184_);
                    if lean_obj_tag(v___x_2185_) == 1 {
                        v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
                        lean_inc(v_val_2186_);
                        lean_dec_ref_known(v___x_2185_, 1);
                        v___x_2187_ = lean_st_ref_take(v_a_2162_);
                        v___x_2188_ =
                            l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__2;
                        v___x_2189_ =
                            l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___closed__3;
                        v___x_2190_ = 0;
                        v___x_2191_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2191_, 0, v_stx_2161_);
                        lean_ctor_set_uint8(
                            v___x_2191_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2190_,
                        );
                        v___x_2192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                            v___x_2188_,
                            v___x_2189_,
                            v___x_2187_,
                            v_val_2186_,
                            v___x_2191_,
                        );
                        v___x_2193_ = lean_st_ref_set(v_a_2162_, v___x_2192_);
                        v___y_2169_ = v_a_2162_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2185_);
                        lean_dec_ref_known(v_stx_2161_, 3);
                        v___y_2169_ = v_a_2162_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___lam__0(
    mut v_x_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ =
        l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v___y_2200_, v___y_2201_);
    return v___x_2203_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg___boxed(
    mut v_stx_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2207_: *mut LeanObject = core::ptr::null_mut();
    v_res_2207_ =
        l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_2204_, v_a_2205_);
    lean_dec(v_a_2205_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(
    mut v_00_u03c9_2208_: *mut LeanObject,
    mut v_stx_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2212_ =
        l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_2209_, v_a_2210_);
    return v___x_2212_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___boxed(
    mut v_00_u03c9_2213_: *mut LeanObject,
    mut v_stx_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2217_: *mut LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics(
        v_00_u03c9_2213_,
        v_stx_2214_,
        v_a_2215_,
    );
    lean_dec(v_a_2215_);
    return v_res_2217_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(
    mut v_x_2218_: *mut LeanObject,
    mut v_x_2219_: *mut LeanObject,
    mut v_x_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2220_) == 0 {
                    lean_dec_ref(v_x_2219_);
                    v___x_2221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2221_, 0, v_x_2218_);
                    return v___x_2221_;
                } else {
                    lean_dec_ref(v_x_2218_);
                    v_head_2222_ = lean_ctor_get(v_x_2220_, 0);
                    v_tail_2223_ = lean_ctor_get(v_x_2220_, 1);
                    v_fst_2224_ = lean_ctor_get(v_head_2222_, 0);
                    v_snd_2225_ = lean_ctor_get(v_head_2222_, 1);
                    v_size_2226_ = lean_ctor_get(v_x_2219_, 2);
                    v___x_2227_ = lean_nat_dec_eq(v_size_2226_, v_fst_2224_);
                    if v___x_2227_ == 0 {
                        lean_dec_ref(v_x_2219_);
                        v___x_2228_ = lean_box(0);
                        return v___x_2228_;
                    } else {
                        v___x_2229_ = l_Lean_Elab_instInhabitedInfoTree_default;
                        v___x_2230_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_2229_,
                            v_x_2219_,
                            v_snd_2225_,
                        );
                        lean_dec_ref(v_x_2219_);
                        if lean_obj_tag(v___x_2230_) == 1 {
                            v_i_2231_ = lean_ctor_get(v___x_2230_, 0);
                            lean_inc_ref(v_i_2231_);
                            v_children_2232_ = lean_ctor_get(v___x_2230_, 1);
                            lean_inc_ref(v_children_2232_);
                            lean_dec_ref_known(v___x_2230_, 2);
                            v_x_2218_ = v_i_2231_;
                            v_x_2219_ = v_children_2232_;
                            v_x_2220_ = v_tail_2223_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v___x_2230_);
                            v___x_2234_ = lean_box(0);
                            return v___x_2234_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath___boxed(
    mut v_x_2235_: *mut LeanObject,
    mut v_x_2236_: *mut LeanObject,
    mut v_x_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2238_: *mut LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(v_x_2235_, v_x_2236_, v_x_2237_);
    lean_dec(v_x_2237_);
    return v_res_2238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(
    mut v_x_2239_: *mut LeanObject,
    mut v_x_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u64 = 0;
    let mut v___x_2249_: u64 = 0;
    let mut v___x_2250_: u64 = 0;
    let mut v_fold_2251_: u64 = 0;
    let mut v___x_2252_: u64 = 0;
    let mut v___x_2253_: u64 = 0;
    let mut v___x_2254_: u64 = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: usize = 0;
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2240_) == 0 {
                    return v_x_2239_;
                } else {
                    v_key_2241_ = lean_ctor_get(v_x_2240_, 0);
                    v_value_2242_ = lean_ctor_get(v_x_2240_, 1);
                    v_tail_2243_ = lean_ctor_get(v_x_2240_, 2);
                    v_isSharedCheck_2266_ = (!lean_is_exclusive(v_x_2240_)) as u8;
                    if v_isSharedCheck_2266_ == 0 {
                        v___x_2245_ = v_x_2240_;
                        v_isShared_2246_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2243_);
                        lean_inc(v_value_2242_);
                        lean_inc(v_key_2241_);
                        lean_dec(v_x_2240_);
                        v___x_2245_ = lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2247_ = lean_array_get_size(v_x_2239_);
                v___x_2248_ = l_Lean_Syntax_instHashableRange_hash(v_key_2241_);
                v___x_2249_ = 32u64;
                v___x_2250_ = lean_uint64_shift_right(v___x_2248_, v___x_2249_);
                v_fold_2251_ = lean_uint64_xor(v___x_2248_, v___x_2250_);
                v___x_2252_ = 16u64;
                v___x_2253_ = lean_uint64_shift_right(v_fold_2251_, v___x_2252_);
                v___x_2254_ = lean_uint64_xor(v_fold_2251_, v___x_2253_);
                v___x_2255_ = lean_uint64_to_usize(v___x_2254_);
                v___x_2256_ = lean_usize_of_nat(v___x_2247_);
                v___x_2257_ = 1usize;
                v___x_2258_ = lean_usize_sub(v___x_2256_, v___x_2257_);
                v___x_2259_ = lean_usize_land(v___x_2255_, v___x_2258_);
                v___x_2260_ = lean_array_uget_borrowed(v_x_2239_, v___x_2259_);
                lean_inc(v___x_2260_);
                if v_isShared_2246_ == 0 {
                    lean_ctor_set(v___x_2245_, 2, v___x_2260_);
                    v___x_2262_ = v___x_2245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_key_2241_);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_value_2242_);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 2, v___x_2260_);
                    v___x_2262_ = v_reuseFailAlloc_2265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2263_ = lean_array_uset(v_x_2239_, v___x_2259_, v___x_2262_);
                v_x_2239_ = v___x_2263_;
                v_x_2240_ = v_tail_2243_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(
    mut v_i_2267_: *mut LeanObject,
    mut v_source_2268_: *mut LeanObject,
    mut v_target_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v_es_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2270_ = lean_array_get_size(v_source_2268_);
                v___x_2271_ = lean_nat_dec_lt(v_i_2267_, v___x_2270_);
                if v___x_2271_ == 0 {
                    lean_dec_ref(v_source_2268_);
                    lean_dec(v_i_2267_);
                    return v_target_2269_;
                } else {
                    v_es_2272_ = lean_array_fget(v_source_2268_, v_i_2267_);
                    v___x_2273_ = lean_box(0);
                    v_source_2274_ = lean_array_fset(v_source_2268_, v_i_2267_, v___x_2273_);
                    v_target_2275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_target_2269_, v_es_2272_);
                    v___x_2276_ = lean_unsigned_to_nat(1);
                    v___x_2277_ = lean_nat_add(v_i_2267_, v___x_2276_);
                    lean_dec(v_i_2267_);
                    v_i_2267_ = v___x_2277_;
                    v_source_2268_ = v_source_2274_;
                    v_target_2269_ = v_target_2275_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(
    mut v_data_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = lean_array_get_size(v_data_2279_);
    v___x_2281_ = lean_unsigned_to_nat(2);
    v_nbuckets_2282_ = lean_nat_mul(v___x_2280_, v___x_2281_);
    v___x_2283_ = lean_unsigned_to_nat(0);
    v___x_2284_ = lean_box(0);
    v___x_2285_ = lean_mk_array(v_nbuckets_2282_, v___x_2284_);
    v___x_2286_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v___x_2283_, v_data_2279_, v___x_2285_);
    return v___x_2286_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(
    mut v_a_2287_: *mut LeanObject,
    mut v_b_2288_: *mut LeanObject,
    mut v_x_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2296_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2289_) == 0 {
                    lean_dec(v_b_2288_);
                    lean_dec_ref(v_a_2287_);
                    return v_x_2289_;
                } else {
                    v_key_2290_ = lean_ctor_get(v_x_2289_, 0);
                    v_value_2291_ = lean_ctor_get(v_x_2289_, 1);
                    v_tail_2292_ = lean_ctor_get(v_x_2289_, 2);
                    v_isSharedCheck_2304_ = (!lean_is_exclusive(v_x_2289_)) as u8;
                    if v_isSharedCheck_2304_ == 0 {
                        v___x_2294_ = v_x_2289_;
                        v_isShared_2295_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2292_);
                        lean_inc(v_value_2291_);
                        lean_inc(v_key_2290_);
                        lean_dec(v_x_2289_);
                        v___x_2294_ = lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2296_ = l_Lean_Syntax_instBEqRange_beq(v_key_2290_, v_a_2287_);
                if v___x_2296_ == 0 {
                    v___x_2297_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_2287_, v_b_2288_, v_tail_2292_);
                    if v_isShared_2295_ == 0 {
                        lean_ctor_set(v___x_2294_, 2, v___x_2297_);
                        v___x_2299_ = v___x_2294_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_key_2290_);
                        lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_value_2291_);
                        lean_ctor_set(v_reuseFailAlloc_2300_, 2, v___x_2297_);
                        v___x_2299_ = v_reuseFailAlloc_2300_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2291_);
                    lean_dec(v_key_2290_);
                    if v_isShared_2295_ == 0 {
                        lean_ctor_set(v___x_2294_, 1, v_b_2288_);
                        lean_ctor_set(v___x_2294_, 0, v_a_2287_);
                        v___x_2302_ = v___x_2294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2287_);
                        lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_b_2288_);
                        lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_tail_2292_);
                        v___x_2302_ = v_reuseFailAlloc_2303_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2299_;
            }
            3 => {
                return v___x_2302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(
    mut v_a_2305_: *mut LeanObject,
    mut v_x_2306_: *mut LeanObject,
) -> u8 {
    let mut v___x_2307_: u8 = 0;
    let mut v_key_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2306_) == 0 {
                    v___x_2307_ = 0;
                    return v___x_2307_;
                } else {
                    v_key_2308_ = lean_ctor_get(v_x_2306_, 0);
                    v_tail_2309_ = lean_ctor_get(v_x_2306_, 2);
                    v___x_2310_ = l_Lean_Syntax_instBEqRange_beq(v_key_2308_, v_a_2305_);
                    if v___x_2310_ == 0 {
                        v_x_2306_ = v_tail_2309_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2310_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg___boxed(
    mut v_a_2312_: *mut LeanObject,
    mut v_x_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2314_: u8 = 0;
    let mut v_r_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_2312_, v_x_2313_);
    lean_dec(v_x_2313_);
    lean_dec_ref(v_a_2312_);
    v_r_2315_ = lean_box((v_res_2314_) as usize);
    return v_r_2315_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(
    mut v_m_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_b_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u64 = 0;
    let mut v___x_2326_: u64 = 0;
    let mut v___x_2327_: u64 = 0;
    let mut v_fold_2328_: u64 = 0;
    let mut v___x_2329_: u64 = 0;
    let mut v___x_2330_: u64 = 0;
    let mut v___x_2331_: u64 = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: usize = 0;
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: usize = 0;
    let mut v___x_2336_: usize = 0;
    let mut v_bkt_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v_val_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2319_ = lean_ctor_get(v_m_2316_, 0);
                v_buckets_2320_ = lean_ctor_get(v_m_2316_, 1);
                v_isSharedCheck_2363_ = (!lean_is_exclusive(v_m_2316_)) as u8;
                if v_isSharedCheck_2363_ == 0 {
                    v___x_2322_ = v_m_2316_;
                    v_isShared_2323_ = v_isSharedCheck_2363_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2320_);
                    lean_inc(v_size_2319_);
                    lean_dec(v_m_2316_);
                    v___x_2322_ = lean_box(0);
                    v_isShared_2323_ = v_isSharedCheck_2363_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2324_ = lean_array_get_size(v_buckets_2320_);
                v___x_2325_ = l_Lean_Syntax_instHashableRange_hash(v_a_2317_);
                v___x_2326_ = 32u64;
                v___x_2327_ = lean_uint64_shift_right(v___x_2325_, v___x_2326_);
                v_fold_2328_ = lean_uint64_xor(v___x_2325_, v___x_2327_);
                v___x_2329_ = 16u64;
                v___x_2330_ = lean_uint64_shift_right(v_fold_2328_, v___x_2329_);
                v___x_2331_ = lean_uint64_xor(v_fold_2328_, v___x_2330_);
                v___x_2332_ = lean_uint64_to_usize(v___x_2331_);
                v___x_2333_ = lean_usize_of_nat(v___x_2324_);
                v___x_2334_ = 1usize;
                v___x_2335_ = lean_usize_sub(v___x_2333_, v___x_2334_);
                v___x_2336_ = lean_usize_land(v___x_2332_, v___x_2335_);
                v_bkt_2337_ = lean_array_uget_borrowed(v_buckets_2320_, v___x_2336_);
                v___x_2338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_2317_, v_bkt_2337_);
                if v___x_2338_ == 0 {
                    v___x_2339_ = lean_unsigned_to_nat(1);
                    v_size_x27_2340_ = lean_nat_add(v_size_2319_, v___x_2339_);
                    lean_dec(v_size_2319_);
                    lean_inc(v_bkt_2337_);
                    v___x_2341_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2341_, 0, v_a_2317_);
                    lean_ctor_set(v___x_2341_, 1, v_b_2318_);
                    lean_ctor_set(v___x_2341_, 2, v_bkt_2337_);
                    v_buckets_x27_2342_ =
                        lean_array_uset(v_buckets_2320_, v___x_2336_, v___x_2341_);
                    v___x_2343_ = lean_unsigned_to_nat(4);
                    v___x_2344_ = lean_nat_mul(v_size_x27_2340_, v___x_2343_);
                    v___x_2345_ = lean_unsigned_to_nat(3);
                    v___x_2346_ = lean_nat_div(v___x_2344_, v___x_2345_);
                    lean_dec(v___x_2344_);
                    v___x_2347_ = lean_array_get_size(v_buckets_x27_2342_);
                    v___x_2348_ = lean_nat_dec_le(v___x_2346_, v___x_2347_);
                    lean_dec(v___x_2346_);
                    if v___x_2348_ == 0 {
                        v_val_2349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_buckets_x27_2342_);
                        if v_isShared_2323_ == 0 {
                            lean_ctor_set(v___x_2322_, 1, v_val_2349_);
                            lean_ctor_set(v___x_2322_, 0, v_size_x27_2340_);
                            v___x_2351_ = v___x_2322_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_size_x27_2340_);
                            lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_val_2349_);
                            v___x_2351_ = v_reuseFailAlloc_2352_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2323_ == 0 {
                            lean_ctor_set(v___x_2322_, 1, v_buckets_x27_2342_);
                            lean_ctor_set(v___x_2322_, 0, v_size_x27_2340_);
                            v___x_2354_ = v___x_2322_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_size_x27_2340_);
                            lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_buckets_x27_2342_);
                            v___x_2354_ = v_reuseFailAlloc_2355_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2337_);
                    v___x_2356_ = lean_box(0);
                    v_buckets_x27_2357_ =
                        lean_array_uset(v_buckets_2320_, v___x_2336_, v___x_2356_);
                    v___x_2358_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_2317_, v_b_2318_, v_bkt_2337_);
                    v___x_2359_ = lean_array_uset(v_buckets_x27_2357_, v___x_2336_, v___x_2358_);
                    if v_isShared_2323_ == 0 {
                        lean_ctor_set(v___x_2322_, 1, v___x_2359_);
                        v___x_2361_ = v___x_2322_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_size_2319_);
                        lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2359_);
                        v___x_2361_ = v_reuseFailAlloc_2362_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2351_;
            }
            3 => {
                return v___x_2354_;
            }
            4 => {
                return v___x_2361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(
    mut v_a_2364_: *mut LeanObject,
    mut v_x_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2371_: u8 = 0;
    let mut v___x_2372_: u8 = 0;
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2365_) == 0 {
                    return v_x_2365_;
                } else {
                    v_key_2366_ = lean_ctor_get(v_x_2365_, 0);
                    v_value_2367_ = lean_ctor_get(v_x_2365_, 1);
                    v_tail_2368_ = lean_ctor_get(v_x_2365_, 2);
                    v_isSharedCheck_2377_ = (!lean_is_exclusive(v_x_2365_)) as u8;
                    if v_isSharedCheck_2377_ == 0 {
                        v___x_2370_ = v_x_2365_;
                        v_isShared_2371_ = v_isSharedCheck_2377_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2368_);
                        lean_inc(v_value_2367_);
                        lean_inc(v_key_2366_);
                        lean_dec(v_x_2365_);
                        v___x_2370_ = lean_box(0);
                        v_isShared_2371_ = v_isSharedCheck_2377_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2372_ = l_Lean_Syntax_instBEqRange_beq(v_key_2366_, v_a_2364_);
                if v___x_2372_ == 0 {
                    v___x_2373_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_2364_, v_tail_2368_);
                    if v_isShared_2371_ == 0 {
                        lean_ctor_set(v___x_2370_, 2, v___x_2373_);
                        v___x_2375_ = v___x_2370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_key_2366_);
                        lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_value_2367_);
                        lean_ctor_set(v_reuseFailAlloc_2376_, 2, v___x_2373_);
                        v___x_2375_ = v_reuseFailAlloc_2376_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2370_);
                    lean_dec(v_value_2367_);
                    lean_dec(v_key_2366_);
                    return v_tail_2368_;
                }
            }
            2 => {
                return v___x_2375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg___boxed(
    mut v_a_2378_: *mut LeanObject,
    mut v_x_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2380_: *mut LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_2378_, v_x_2379_);
    lean_dec_ref(v_a_2378_);
    return v_res_2380_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(
    mut v_m_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: u64 = 0;
    let mut v___x_2387_: u64 = 0;
    let mut v___x_2388_: u64 = 0;
    let mut v_fold_2389_: u64 = 0;
    let mut v___x_2390_: u64 = 0;
    let mut v___x_2391_: u64 = 0;
    let mut v___x_2392_: u64 = 0;
    let mut v___x_2393_: usize = 0;
    let mut v___x_2394_: usize = 0;
    let mut v___x_2395_: usize = 0;
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v_bkt_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2412_: u8 = 0;
    let mut v_unused_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2383_ = lean_ctor_get(v_m_2381_, 0);
                v_buckets_2384_ = lean_ctor_get(v_m_2381_, 1);
                v___x_2385_ = lean_array_get_size(v_buckets_2384_);
                v___x_2386_ = l_Lean_Syntax_instHashableRange_hash(v_a_2382_);
                v___x_2387_ = 32u64;
                v___x_2388_ = lean_uint64_shift_right(v___x_2386_, v___x_2387_);
                v_fold_2389_ = lean_uint64_xor(v___x_2386_, v___x_2388_);
                v___x_2390_ = 16u64;
                v___x_2391_ = lean_uint64_shift_right(v_fold_2389_, v___x_2390_);
                v___x_2392_ = lean_uint64_xor(v_fold_2389_, v___x_2391_);
                v___x_2393_ = lean_uint64_to_usize(v___x_2392_);
                v___x_2394_ = lean_usize_of_nat(v___x_2385_);
                v___x_2395_ = 1usize;
                v___x_2396_ = lean_usize_sub(v___x_2394_, v___x_2395_);
                v___x_2397_ = lean_usize_land(v___x_2393_, v___x_2396_);
                v_bkt_2398_ = lean_array_uget_borrowed(v_buckets_2384_, v___x_2397_);
                v___x_2399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_2382_, v_bkt_2398_);
                if v___x_2399_ == 0 {
                    return v_m_2381_;
                } else {
                    lean_inc(v_bkt_2398_);
                    lean_inc_ref(v_buckets_2384_);
                    lean_inc(v_size_2383_);
                    v_isSharedCheck_2412_ = (!lean_is_exclusive(v_m_2381_)) as u8;
                    if v_isSharedCheck_2412_ == 0 {
                        v_unused_2413_ = lean_ctor_get(v_m_2381_, 1);
                        lean_dec(v_unused_2413_);
                        v_unused_2414_ = lean_ctor_get(v_m_2381_, 0);
                        lean_dec(v_unused_2414_);
                        v___x_2401_ = v_m_2381_;
                        v_isShared_2402_ = v_isSharedCheck_2412_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2381_);
                        v___x_2401_ = lean_box(0);
                        v_isShared_2402_ = v_isSharedCheck_2412_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2403_ = lean_box(0);
                v_buckets_x27_2404_ = lean_array_uset(v_buckets_2384_, v___x_2397_, v___x_2403_);
                v___x_2405_ = lean_unsigned_to_nat(1);
                v___x_2406_ = lean_nat_sub(v_size_2383_, v___x_2405_);
                lean_dec(v_size_2383_);
                v___x_2407_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_2382_, v_bkt_2398_);
                v___x_2408_ = lean_array_uset(v_buckets_x27_2404_, v___x_2397_, v___x_2407_);
                if v_isShared_2402_ == 0 {
                    lean_ctor_set(v___x_2401_, 1, v___x_2408_);
                    lean_ctor_set(v___x_2401_, 0, v___x_2406_);
                    v___x_2410_ = v___x_2401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2406_);
                    lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2408_);
                    v___x_2410_ = v_reuseFailAlloc_2411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg___boxed(
    mut v_m_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_2415_, v_a_2416_);
    lean_dec_ref(v_a_2416_);
    return v_res_2417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(
    mut v_a_2418_: *mut LeanObject,
    mut v_x_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2419_) == 0 {
                    v___x_2420_ = lean_box(0);
                    return v___x_2420_;
                } else {
                    v_key_2421_ = lean_ctor_get(v_x_2419_, 0);
                    v_value_2422_ = lean_ctor_get(v_x_2419_, 1);
                    v_tail_2423_ = lean_ctor_get(v_x_2419_, 2);
                    v___x_2424_ = l_Lean_Syntax_instBEqRange_beq(v_key_2421_, v_a_2418_);
                    if v___x_2424_ == 0 {
                        v_x_2419_ = v_tail_2423_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2422_);
                        v___x_2426_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2426_, 0, v_value_2422_);
                        return v___x_2426_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg___boxed(
    mut v_a_2427_: *mut LeanObject,
    mut v_x_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2429_: *mut LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_2427_, v_x_2428_);
    lean_dec(v_x_2428_);
    lean_dec_ref(v_a_2427_);
    return v_res_2429_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(
    mut v_m_2430_: *mut LeanObject,
    mut v_a_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u64 = 0;
    let mut v___x_2435_: u64 = 0;
    let mut v___x_2436_: u64 = 0;
    let mut v_fold_2437_: u64 = 0;
    let mut v___x_2438_: u64 = 0;
    let mut v___x_2439_: u64 = 0;
    let mut v___x_2440_: u64 = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___x_2445_: usize = 0;
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2432_ = lean_ctor_get(v_m_2430_, 1);
    v___x_2433_ = lean_array_get_size(v_buckets_2432_);
    v___x_2434_ = l_Lean_Syntax_instHashableRange_hash(v_a_2431_);
    v___x_2435_ = 32u64;
    v___x_2436_ = lean_uint64_shift_right(v___x_2434_, v___x_2435_);
    v_fold_2437_ = lean_uint64_xor(v___x_2434_, v___x_2436_);
    v___x_2438_ = 16u64;
    v___x_2439_ = lean_uint64_shift_right(v_fold_2437_, v___x_2438_);
    v___x_2440_ = lean_uint64_xor(v_fold_2437_, v___x_2439_);
    v___x_2441_ = lean_uint64_to_usize(v___x_2440_);
    v___x_2442_ = lean_usize_of_nat(v___x_2433_);
    v___x_2443_ = 1usize;
    v___x_2444_ = lean_usize_sub(v___x_2442_, v___x_2443_);
    v___x_2445_ = lean_usize_land(v___x_2441_, v___x_2444_);
    v___x_2446_ = lean_array_uget_borrowed(v_buckets_2432_, v___x_2445_);
    v___x_2447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_2431_, v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg___boxed(
    mut v_m_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_2448_, v_a_2449_);
    lean_dec_ref(v_a_2449_);
    lean_dec_ref(v_m_2448_);
    return v_res_2450_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2451_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_2451_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = lean_unsigned_to_nat(5);
    v___x_2453_ = lean_unsigned_to_nat(0);
    v___x_2454_ = lean_nat_mod(v___x_2453_, v___x_2452_);
    return v___x_2454_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__4,
    );
    v___x_2456_ = lean_unsigned_to_nat(5);
    v___x_2457_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2457_, 0, v___x_2456_);
    lean_ctor_set(v___x_2457_, 1, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2458_ = lean_box(0);
    v___x_2459_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__5,
    );
    v___x_2460_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2460_, 0, v___x_2459_);
    lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___x_2461_ = lean_unsigned_to_nat(1);
    v___x_2462_ = lean_unsigned_to_nat(0);
    v___x_2463_ = lean_nat_mod(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__0,
    );
    v___x_2465_ = lean_unsigned_to_nat(1);
    v___x_2466_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2466_, 0, v___x_2465_);
    lean_ctor_set(v___x_2466_, 1, v___x_2464_);
    return v___x_2466_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__6,
    );
    v___x_2468_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2469_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2469_, 0, v___x_2468_);
    lean_ctor_set(v___x_2469_, 1, v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = lean_unsigned_to_nat(2);
    v___x_2471_ = lean_unsigned_to_nat(1);
    v___x_2472_ = lean_nat_mod(v___x_2471_, v___x_2470_);
    return v___x_2472_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__2,
    );
    v___x_2474_ = lean_unsigned_to_nat(2);
    v___x_2475_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2475_, 0, v___x_2474_);
    lean_ctor_set(v___x_2475_, 1, v___x_2473_);
    return v___x_2475_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__7,
    );
    v___x_2477_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__3,
    );
    v___x_2478_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2478_, 0, v___x_2477_);
    lean_ctor_set(v___x_2478_, 1, v___x_2476_);
    return v___x_2478_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__8,
    );
    v___x_2480_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2481_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2481_, 0, v___x_2480_);
    lean_ctor_set(v___x_2481_, 1, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9,
    );
    v___x_2485_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2486_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2486_, 0, v___x_2485_);
    lean_ctor_set(v___x_2486_, 1, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2487_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__11,
    );
    v___x_2488_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2489_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2489_, 0, v___x_2488_);
    lean_ctor_set(v___x_2489_, 1, v___x_2487_);
    return v___x_2489_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2490_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__12,
    );
    v___x_2491_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2492_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2492_, 0, v___x_2491_);
    lean_ctor_set(v___x_2492_, 1, v___x_2490_);
    return v___x_2492_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    v___x_2493_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__13,
    );
    v___x_2494_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1_once
        ),
        _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__1,
    );
    v___x_2495_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2495_, 0, v___x_2494_);
    lean_ctor_set(v___x_2495_, 1, v___x_2493_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(
    mut v_multigoals_2496_: *mut LeanObject,
    mut v_x_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: u8 = 0;
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___y_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2567_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___y_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2588_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_2497_) {
                    0 => {
                        v_t_2500_ = lean_ctor_get(v_x_2497_, 1);
                        lean_inc_ref(v_t_2500_);
                        lean_dec_ref_known(v_x_2497_, 2);
                        v_x_2497_ = v_t_2500_;
                        state = 0;
                        continue;
                    }
                    1 => {
                        v_i_2502_ = lean_ctor_get(v_x_2497_, 0);
                        lean_inc_ref(v_i_2502_);
                        v_children_2503_ = lean_ctor_get(v_x_2497_, 1);
                        lean_inc_ref(v_children_2503_);
                        lean_dec_ref_known(v_x_2497_, 2);
                        if lean_obj_tag(v_i_2502_) == 0 {
                            v_i_2512_ = lean_ctor_get(v_i_2502_, 0);
                            v_toElabInfo_2513_ = lean_ctor_get(v_i_2512_, 0);
                            v_goalsBefore_2514_ = lean_ctor_get(v_i_2512_, 2);
                            v_stx_2515_ = lean_ctor_get(v_toElabInfo_2513_, 1);
                            v___x_2516_ = 1;
                            v___x_2517_ = l_Lean_Syntax_getRange_x3f(v_stx_2515_, v___x_2516_);
                            if lean_obj_tag(v___x_2517_) == 1 {
                                v_val_2518_ = lean_ctor_get(v___x_2517_, 0);
                                lean_inc(v_val_2518_);
                                lean_dec_ref_known(v___x_2517_, 1);
                                v___x_2522_ = lean_st_ref_get(v_a_2498_);
                                v___x_2523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v___x_2522_, v_val_2518_);
                                lean_dec(v___x_2522_);
                                if lean_obj_tag(v___x_2523_) == 1 {
                                    v_val_2524_ = lean_ctor_get(v___x_2523_, 0);
                                    lean_inc(v_val_2524_);
                                    lean_dec_ref_known(v___x_2523_, 1);
                                    lean_inc(v_stx_2515_);
                                    v___x_2538_ = l_Lean_Syntax_getKind(v_stx_2515_);
                                    v___x_2539_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__1;
                                    v___x_2540_ = lean_name_eq(v___x_2538_, v___x_2539_);
                                    if v___x_2540_ == 0 {
                                        v___x_2569_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_isSeqFocus___closed__3;
                                        v___x_2570_ = lean_name_eq(v___x_2538_, v___x_2569_);
                                        lean_dec(v___x_2538_);
                                        if v___x_2570_ == 0 {
                                            lean_dec(v_val_2524_);
                                            lean_dec(v_val_2518_);
                                            lean_dec_ref_known(v_i_2502_, 1);
                                            v___x_2590_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_2496_, v_children_2503_, v_a_2498_);
                                            lean_dec_ref(v_children_2503_);
                                            return v___x_2590_;
                                        } else {
                                            v___x_2591_ =
                                                l_List_lengthTR___redArg(v_goalsBefore_2514_);
                                            v___x_2592_ = lean_unsigned_to_nat(1);
                                            v___x_2593_ = lean_nat_dec_eq(v___x_2591_, v___x_2592_);
                                            lean_dec(v___x_2591_);
                                            if v___x_2593_ == 0 {
                                                v___x_2594_ = lean_unsigned_to_nat(0);
                                                v___x_2595_ =
                                                    l_Lean_Syntax_getArg(v_stx_2515_, v___x_2594_);
                                                v___x_2596_ = l_Lean_Syntax_getKind(v___x_2595_);
                                                v___x_2597_ = l_Lean_NameSet_contains(
                                                    v_multigoals_2496_,
                                                    v___x_2596_,
                                                );
                                                lean_dec(v___x_2596_);
                                                if v___x_2597_ == 0 {
                                                    v___y_2588_ = v___x_2570_;
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    v___y_2588_ = v___x_2593_;
                                                    state = 14;
                                                    continue;
                                                }
                                            } else {
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_2538_);
                                        v___x_2598_ = l_List_lengthTR___redArg(v_goalsBefore_2514_);
                                        v___x_2599_ = lean_unsigned_to_nat(1);
                                        v___x_2600_ = lean_nat_dec_eq(v___x_2598_, v___x_2599_);
                                        lean_dec(v___x_2598_);
                                        if v___x_2600_ == 0 {
                                            v___x_2601_ = lean_unsigned_to_nat(0);
                                            v___x_2602_ =
                                                l_Lean_Syntax_getArg(v_stx_2515_, v___x_2601_);
                                            v___x_2603_ = l_Lean_Syntax_getKind(v___x_2602_);
                                            v___x_2604_ = l_Lean_NameSet_contains(
                                                v_multigoals_2496_,
                                                v___x_2603_,
                                            );
                                            lean_dec(v___x_2603_);
                                            if v___x_2604_ == 0 {
                                                v___y_2567_ = v___x_2540_;
                                                state = 11;
                                                continue;
                                            } else {
                                                v___y_2567_ = v___x_2600_;
                                                state = 11;
                                                continue;
                                            }
                                        } else {
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_2523_);
                                    lean_dec(v_val_2518_);
                                    lean_dec_ref_known(v_i_2502_, 1);
                                    v___x_2605_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_2496_, v_children_2503_, v_a_2498_);
                                    lean_dec_ref(v_children_2503_);
                                    return v___x_2605_;
                                }
                            } else {
                                lean_dec(v___x_2517_);
                                lean_dec_ref_known(v_i_2502_, 1);
                                v___x_2606_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_2496_, v_children_2503_, v_a_2498_);
                                lean_dec_ref(v_children_2503_);
                                return v___x_2606_;
                            }
                        } else {
                            lean_dec_ref(v_i_2502_);
                            v___x_2607_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(v_multigoals_2496_, v_children_2503_, v_a_2498_);
                            lean_dec_ref(v_children_2503_);
                            return v___x_2607_;
                        }
                    }
                    _ => {
                        lean_dec_ref_known(v_x_2497_, 1);
                        v___x_2608_ = lean_box(0);
                        return v___x_2608_;
                    }
                }
            }
            1 => {
                v___x_2506_ = lean_st_ref_set(v_a_2498_, v_snd_2505_);
                v___x_2507_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
                    v_multigoals_2496_,
                    v_children_2503_,
                    v_a_2498_,
                );
                lean_dec_ref(v_children_2503_);
                return v___x_2507_;
            }
            2 => {
                v___x_2510_ = lean_st_ref_set(v_a_2498_, v_snd_2509_);
                v___x_2511_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
                    v_multigoals_2496_,
                    v_children_2503_,
                    v_a_2498_,
                );
                lean_dec_ref(v_children_2503_);
                return v___x_2511_;
            }
            3 => {
                v___x_2521_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_2520_, v_val_2518_);
                lean_dec(v_val_2518_);
                v_snd_2505_ = v___x_2521_;
                state = 1;
                continue;
            }
            4 => {
                if v___y_2527_ == 0 {
                    lean_dec(v_val_2524_);
                    v___x_2528_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v___y_2526_, v_val_2518_);
                    lean_dec(v_val_2518_);
                    v_snd_2509_ = v___x_2528_;
                    state = 2;
                    continue;
                } else {
                    v_stx_2529_ = lean_ctor_get(v_val_2524_, 0);
                    v_isSharedCheck_2537_ = (!lean_is_exclusive(v_val_2524_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v___x_2531_ = v_val_2524_;
                        v_isShared_2532_ = v_isSharedCheck_2537_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_stx_2529_);
                        lean_dec(v_val_2524_);
                        v___x_2531_ = lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2537_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2532_ == 0 {
                    v___x_2534_ = v___x_2531_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_stx_2529_);
                    v___x_2534_ = v_reuseFailAlloc_2536_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_ctor_set_uint8(
                    v___x_2534_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2516_,
                );
                v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___y_2526_, v_val_2518_, v___x_2534_);
                v_snd_2509_ = v___x_2535_;
                state = 2;
                continue;
            }
            7 => {
                v___x_2543_ = lean_st_ref_take(v_a_2498_);
                if lean_obj_tag(v___y_2542_) == 0 {
                    lean_dec(v_val_2524_);
                    v___y_2520_ = v___x_2543_;
                    state = 3;
                    continue;
                } else {
                    if v___x_2540_ == 0 {
                        lean_dec(v_val_2524_);
                        v___y_2520_ = v___x_2543_;
                        state = 3;
                        continue;
                    } else {
                        v_stx_2544_ = lean_ctor_get(v_val_2524_, 0);
                        v_isSharedCheck_2552_ = (!lean_is_exclusive(v_val_2524_)) as u8;
                        if v_isSharedCheck_2552_ == 0 {
                            v___x_2546_ = v_val_2524_;
                            v_isShared_2547_ = v_isSharedCheck_2552_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_stx_2544_);
                            lean_dec(v_val_2524_);
                            v___x_2546_ = lean_box(0);
                            v_isShared_2547_ = v_isSharedCheck_2552_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_2547_ == 0 {
                    v___x_2549_ = v___x_2546_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_stx_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2551_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_ctor_set_uint8(
                    v___x_2549_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2516_,
                );
                v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v___x_2543_, v_val_2518_, v___x_2549_);
                v_snd_2505_ = v___x_2550_;
                state = 1;
                continue;
            }
            10 => {
                v___x_2554_ = lean_unsigned_to_nat(1);
                v___x_2555_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9_once), _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__9);
                lean_inc_ref(v_children_2503_);
                v___x_2556_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(
                    v_i_2502_,
                    v_children_2503_,
                    v___x_2555_,
                );
                if lean_obj_tag(v___x_2556_) == 0 {
                    v___x_2557_ = lean_box(0);
                    v___y_2542_ = v___x_2557_;
                    state = 7;
                    continue;
                } else {
                    v_val_2558_ = lean_ctor_get(v___x_2556_, 0);
                    lean_inc(v_val_2558_);
                    lean_dec_ref_known(v___x_2556_, 1);
                    if lean_obj_tag(v_val_2558_) == 0 {
                        v_i_2559_ = lean_ctor_get(v_val_2558_, 0);
                        lean_inc_ref(v_i_2559_);
                        lean_dec_ref_known(v_val_2558_, 1);
                        v_goalsAfter_2560_ = lean_ctor_get(v_i_2559_, 4);
                        lean_inc(v_goalsAfter_2560_);
                        lean_dec_ref(v_i_2559_);
                        v___x_2561_ = l_List_lengthTR___redArg(v_goalsAfter_2560_);
                        lean_dec(v_goalsAfter_2560_);
                        v___x_2562_ = lean_nat_dec_eq(v___x_2561_, v___x_2554_);
                        lean_dec(v___x_2561_);
                        if v___x_2562_ == 0 {
                            v___x_2563_ = lean_box(0);
                            v___y_2542_ = v___x_2563_;
                            state = 7;
                            continue;
                        } else {
                            v___x_2564_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10;
                            v___y_2542_ = v___x_2564_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2558_);
                        v___x_2565_ = lean_box(0);
                        v___y_2542_ = v___x_2565_;
                        state = 7;
                        continue;
                    }
                }
            }
            11 => {
                if v___y_2567_ == 0 {
                    lean_dec_ref_known(v_i_2502_, 1);
                    v___x_2568_ = lean_box(0);
                    v___y_2542_ = v___x_2568_;
                    state = 7;
                    continue;
                } else {
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_2573_ = lean_st_ref_take(v_a_2498_);
                if lean_obj_tag(v___y_2572_) == 0 {
                    v___y_2526_ = v___x_2573_;
                    v___y_2527_ = v___x_2540_;
                    state = 4;
                    continue;
                } else {
                    v___y_2526_ = v___x_2573_;
                    v___y_2527_ = v___x_2570_;
                    state = 4;
                    continue;
                }
            }
            13 => {
                v___x_2575_ = lean_unsigned_to_nat(1);
                v___x_2576_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14_once), _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__14);
                lean_inc_ref(v_children_2503_);
                v___x_2577_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_getPath(
                    v_i_2502_,
                    v_children_2503_,
                    v___x_2576_,
                );
                if lean_obj_tag(v___x_2577_) == 0 {
                    v___x_2578_ = lean_box(0);
                    v___y_2572_ = v___x_2578_;
                    state = 12;
                    continue;
                } else {
                    v_val_2579_ = lean_ctor_get(v___x_2577_, 0);
                    lean_inc(v_val_2579_);
                    lean_dec_ref_known(v___x_2577_, 1);
                    if lean_obj_tag(v_val_2579_) == 0 {
                        v_i_2580_ = lean_ctor_get(v_val_2579_, 0);
                        lean_inc_ref(v_i_2580_);
                        lean_dec_ref_known(v_val_2579_, 1);
                        v_goalsAfter_2581_ = lean_ctor_get(v_i_2580_, 4);
                        lean_inc(v_goalsAfter_2581_);
                        lean_dec_ref(v_i_2580_);
                        v___x_2582_ = l_List_lengthTR___redArg(v_goalsAfter_2581_);
                        lean_dec(v_goalsAfter_2581_);
                        v___x_2583_ = lean_nat_dec_eq(v___x_2582_, v___x_2575_);
                        lean_dec(v___x_2582_);
                        if v___x_2583_ == 0 {
                            v___x_2584_ = lean_box(0);
                            v___y_2572_ = v___x_2584_;
                            state = 12;
                            continue;
                        } else {
                            v___x_2585_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___closed__10;
                            v___y_2572_ = v___x_2585_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2579_);
                        v___x_2586_ = lean_box(0);
                        v___y_2572_ = v___x_2586_;
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                if v___y_2588_ == 0 {
                    lean_dec_ref_known(v_i_2502_, 1);
                    v___x_2589_ = lean_box(0);
                    v___y_2572_ = v___x_2589_;
                    state = 12;
                    continue;
                } else {
                    state = 13;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(
    mut v_multigoals_2609_: *mut LeanObject,
    mut v_as_2610_: *mut LeanObject,
    mut v_i_2611_: usize,
    mut v_stop_2612_: usize,
    mut v_b_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: usize = 0;
    let mut v___x_2620_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2616_ = lean_usize_dec_eq(v_i_2611_, v_stop_2612_);
                if v___x_2616_ == 0 {
                    v___x_2617_ = lean_array_uget_borrowed(v_as_2610_, v_i_2611_);
                    lean_inc(v___x_2617_);
                    v___x_2618_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(
                        v_multigoals_2609_,
                        v___x_2617_,
                        v___y_2614_,
                    );
                    v___x_2619_ = 1usize;
                    v___x_2620_ = lean_usize_add(v_i_2611_, v___x_2619_);
                    v_i_2611_ = v___x_2620_;
                    v_b_2613_ = v___x_2618_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2613_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(
    mut v_multigoals_2622_: *mut LeanObject,
    mut v_x_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2623_) == 0 {
        let mut v_cs_2626_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2630_: u8 = 0;
        v_cs_2626_ = lean_ctor_get(v_x_2623_, 0);
        v___x_2627_ = lean_unsigned_to_nat(0);
        v___x_2628_ = lean_array_get_size(v_cs_2626_);
        v___x_2629_ = lean_box(0);
        v___x_2630_ = lean_nat_dec_lt(v___x_2627_, v___x_2628_);
        if v___x_2630_ == 0 {
            return v___x_2629_;
        } else {
            let mut v___x_2631_: u8 = 0;
            v___x_2631_ = lean_nat_dec_le(v___x_2628_, v___x_2628_);
            if v___x_2631_ == 0 {
                if v___x_2630_ == 0 {
                    return v___x_2629_;
                } else {
                    let mut v___x_2632_: usize = 0;
                    let mut v___x_2633_: usize = 0;
                    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2632_ = 0usize;
                    v___x_2633_ = lean_usize_of_nat(v___x_2628_);
                    v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2622_, v_cs_2626_, v___x_2632_, v___x_2633_, v___x_2629_, v___y_2624_);
                    return v___x_2634_;
                }
            } else {
                let mut v___x_2635_: usize = 0;
                let mut v___x_2636_: usize = 0;
                let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
                v___x_2635_ = 0usize;
                v___x_2636_ = lean_usize_of_nat(v___x_2628_);
                v___x_2637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2622_, v_cs_2626_, v___x_2635_, v___x_2636_, v___x_2629_, v___y_2624_);
                return v___x_2637_;
            }
        }
    } else {
        let mut v_vs_2638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2642_: u8 = 0;
        v_vs_2638_ = lean_ctor_get(v_x_2623_, 0);
        v___x_2639_ = lean_unsigned_to_nat(0);
        v___x_2640_ = lean_array_get_size(v_vs_2638_);
        v___x_2641_ = lean_box(0);
        v___x_2642_ = lean_nat_dec_lt(v___x_2639_, v___x_2640_);
        if v___x_2642_ == 0 {
            return v___x_2641_;
        } else {
            let mut v___x_2643_: u8 = 0;
            v___x_2643_ = lean_nat_dec_le(v___x_2640_, v___x_2640_);
            if v___x_2643_ == 0 {
                if v___x_2642_ == 0 {
                    return v___x_2641_;
                } else {
                    let mut v___x_2644_: usize = 0;
                    let mut v___x_2645_: usize = 0;
                    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2644_ = 0usize;
                    v___x_2645_ = lean_usize_of_nat(v___x_2640_);
                    v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2622_, v_vs_2638_, v___x_2644_, v___x_2645_, v___x_2641_, v___y_2624_);
                    return v___x_2646_;
                }
            } else {
                let mut v___x_2647_: usize = 0;
                let mut v___x_2648_: usize = 0;
                let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
                v___x_2647_ = 0usize;
                v___x_2648_ = lean_usize_of_nat(v___x_2640_);
                v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2622_, v_vs_2638_, v___x_2647_, v___x_2648_, v___x_2641_, v___y_2624_);
                return v___x_2649_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(
    mut v_multigoals_2650_: *mut LeanObject,
    mut v_as_2651_: *mut LeanObject,
    mut v_i_2652_: usize,
    mut v_stop_2653_: usize,
    mut v_b_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2657_: u8 = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: usize = 0;
    let mut v___x_2661_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = lean_usize_dec_eq(v_i_2652_, v_stop_2653_);
                if v___x_2657_ == 0 {
                    v___x_2658_ = lean_array_uget_borrowed(v_as_2651_, v_i_2652_);
                    v___x_2659_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_2650_, v___x_2658_, v___y_2655_);
                    v___x_2660_ = 1usize;
                    v___x_2661_ = lean_usize_add(v_i_2652_, v___x_2660_);
                    v_i_2652_ = v___x_2661_;
                    v_b_2654_ = v___x_2659_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2654_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(
    mut v_multigoals_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
    mut v_x_2665_: usize,
    mut v_x_2666_: usize,
    mut v___y_2667_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2664_) == 0 {
        let mut v_cs_2669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2671_: usize = 0;
        let mut v_j_2672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2674_: usize = 0;
        let mut v___x_2675_: usize = 0;
        let mut v___x_2676_: usize = 0;
        let mut v___x_2677_: usize = 0;
        let mut v___x_2678_: usize = 0;
        let mut v___x_2679_: usize = 0;
        let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2685_: u8 = 0;
        v_cs_2669_ = lean_ctor_get(v_x_2664_, 0);
        v___x_2670_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___closed__0);
        v___x_2671_ = lean_usize_shift_right(v_x_2665_, v_x_2666_);
        v_j_2672_ = lean_usize_to_nat(v___x_2671_);
        v___x_2673_ = lean_array_get_borrowed(v___x_2670_, v_cs_2669_, v_j_2672_);
        v___x_2674_ = 1usize;
        v___x_2675_ = lean_usize_shift_left(v___x_2674_, v_x_2666_);
        v___x_2676_ = lean_usize_sub(v___x_2675_, v___x_2674_);
        v___x_2677_ = lean_usize_land(v_x_2665_, v___x_2676_);
        v___x_2678_ = 5usize;
        v___x_2679_ = lean_usize_sub(v_x_2666_, v___x_2678_);
        v___x_2680_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_2663_, v___x_2673_, v___x_2677_, v___x_2679_, v___y_2667_);
        v___x_2681_ = lean_unsigned_to_nat(1);
        v___x_2682_ = lean_nat_add(v_j_2672_, v___x_2681_);
        lean_dec(v_j_2672_);
        v___x_2683_ = lean_array_get_size(v_cs_2669_);
        v___x_2684_ = lean_box(0);
        v___x_2685_ = lean_nat_dec_lt(v___x_2682_, v___x_2683_);
        if v___x_2685_ == 0 {
            lean_dec(v___x_2682_);
            return v___x_2684_;
        } else {
            let mut v___x_2686_: u8 = 0;
            v___x_2686_ = lean_nat_dec_le(v___x_2683_, v___x_2683_);
            if v___x_2686_ == 0 {
                if v___x_2685_ == 0 {
                    lean_dec(v___x_2682_);
                    return v___x_2684_;
                } else {
                    let mut v___x_2687_: usize = 0;
                    let mut v___x_2688_: usize = 0;
                    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2687_ = lean_usize_of_nat(v___x_2682_);
                    lean_dec(v___x_2682_);
                    v___x_2688_ = lean_usize_of_nat(v___x_2683_);
                    v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2663_, v_cs_2669_, v___x_2687_, v___x_2688_, v___x_2684_, v___y_2667_);
                    return v___x_2689_;
                }
            } else {
                let mut v___x_2690_: usize = 0;
                let mut v___x_2691_: usize = 0;
                let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
                v___x_2690_ = lean_usize_of_nat(v___x_2682_);
                lean_dec(v___x_2682_);
                v___x_2691_ = lean_usize_of_nat(v___x_2683_);
                v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2663_, v_cs_2669_, v___x_2690_, v___x_2691_, v___x_2684_, v___y_2667_);
                return v___x_2692_;
            }
        }
    } else {
        let mut v_vs_2693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2697_: u8 = 0;
        v_vs_2693_ = lean_ctor_get(v_x_2664_, 0);
        v___x_2694_ = lean_usize_to_nat(v_x_2665_);
        v___x_2695_ = lean_array_get_size(v_vs_2693_);
        v___x_2696_ = lean_box(0);
        v___x_2697_ = lean_nat_dec_lt(v___x_2694_, v___x_2695_);
        if v___x_2697_ == 0 {
            lean_dec(v___x_2694_);
            return v___x_2696_;
        } else {
            let mut v___x_2698_: u8 = 0;
            v___x_2698_ = lean_nat_dec_le(v___x_2695_, v___x_2695_);
            if v___x_2698_ == 0 {
                if v___x_2697_ == 0 {
                    lean_dec(v___x_2694_);
                    return v___x_2696_;
                } else {
                    let mut v___x_2699_: usize = 0;
                    let mut v___x_2700_: usize = 0;
                    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2699_ = lean_usize_of_nat(v___x_2694_);
                    lean_dec(v___x_2694_);
                    v___x_2700_ = lean_usize_of_nat(v___x_2695_);
                    v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2663_, v_vs_2693_, v___x_2699_, v___x_2700_, v___x_2696_, v___y_2667_);
                    return v___x_2701_;
                }
            } else {
                let mut v___x_2702_: usize = 0;
                let mut v___x_2703_: usize = 0;
                let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
                v___x_2702_ = lean_usize_of_nat(v___x_2694_);
                lean_dec(v___x_2694_);
                v___x_2703_ = lean_usize_of_nat(v___x_2695_);
                v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2663_, v_vs_2693_, v___x_2702_, v___x_2703_, v___x_2696_, v___y_2667_);
                return v___x_2704_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(
    mut v_multigoals_2705_: *mut LeanObject,
    mut v_t_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    v_root_2709_ = lean_ctor_get(v_t_2706_, 0);
    v_tail_2710_ = lean_ctor_get(v_t_2706_, 1);
    v___x_2711_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_2705_, v_root_2709_, v___y_2707_);
    v___x_2712_ = lean_unsigned_to_nat(0);
    v___x_2713_ = lean_array_get_size(v_tail_2710_);
    v___x_2714_ = lean_box(0);
    v___x_2715_ = lean_nat_dec_lt(v___x_2712_, v___x_2713_);
    if v___x_2715_ == 0 {
        return v___x_2714_;
    } else {
        let mut v___x_2716_: u8 = 0;
        v___x_2716_ = lean_nat_dec_le(v___x_2713_, v___x_2713_);
        if v___x_2716_ == 0 {
            if v___x_2715_ == 0 {
                return v___x_2714_;
            } else {
                let mut v___x_2717_: usize = 0;
                let mut v___x_2718_: usize = 0;
                let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
                v___x_2717_ = 0usize;
                v___x_2718_ = lean_usize_of_nat(v___x_2713_);
                v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2705_, v_tail_2710_, v___x_2717_, v___x_2718_, v___x_2714_, v___y_2707_);
                return v___x_2719_;
            }
        } else {
            let mut v___x_2720_: usize = 0;
            let mut v___x_2721_: usize = 0;
            let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
            v___x_2720_ = 0usize;
            v___x_2721_ = lean_usize_of_nat(v___x_2713_);
            v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2705_, v_tail_2710_, v___x_2720_, v___x_2721_, v___x_2714_, v___y_2707_);
            return v___x_2722_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(
    mut v_multigoals_2723_: *mut LeanObject,
    mut v_t_2724_: *mut LeanObject,
    mut v_start_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    v___x_2728_ = lean_unsigned_to_nat(0);
    v___x_2729_ = lean_nat_dec_eq(v_start_2725_, v___x_2728_);
    if v___x_2729_ == 0 {
        let mut v_root_2730_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2731_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_2732_: usize = 0;
        let mut v_tailOff_2733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2734_: u8 = 0;
        v_root_2730_ = lean_ctor_get(v_t_2724_, 0);
        v_tail_2731_ = lean_ctor_get(v_t_2724_, 1);
        v_shift_2732_ = lean_ctor_get_usize(v_t_2724_, 4);
        v_tailOff_2733_ = lean_ctor_get(v_t_2724_, 3);
        v___x_2734_ = lean_nat_dec_le(v_tailOff_2733_, v_start_2725_);
        if v___x_2734_ == 0 {
            let mut v___x_2735_: usize = 0;
            let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2739_: u8 = 0;
            v___x_2735_ = lean_usize_of_nat(v_start_2725_);
            v___x_2736_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_2723_, v_root_2730_, v___x_2735_, v_shift_2732_, v___y_2726_);
            v___x_2737_ = lean_array_get_size(v_tail_2731_);
            v___x_2738_ = lean_box(0);
            v___x_2739_ = lean_nat_dec_lt(v___x_2728_, v___x_2737_);
            if v___x_2739_ == 0 {
                return v___x_2738_;
            } else {
                let mut v___x_2740_: u8 = 0;
                v___x_2740_ = lean_nat_dec_le(v___x_2737_, v___x_2737_);
                if v___x_2740_ == 0 {
                    if v___x_2739_ == 0 {
                        return v___x_2738_;
                    } else {
                        let mut v___x_2741_: usize = 0;
                        let mut v___x_2742_: usize = 0;
                        let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2741_ = 0usize;
                        v___x_2742_ = lean_usize_of_nat(v___x_2737_);
                        v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2723_, v_tail_2731_, v___x_2741_, v___x_2742_, v___x_2738_, v___y_2726_);
                        return v___x_2743_;
                    }
                } else {
                    let mut v___x_2744_: usize = 0;
                    let mut v___x_2745_: usize = 0;
                    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2744_ = 0usize;
                    v___x_2745_ = lean_usize_of_nat(v___x_2737_);
                    v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2723_, v_tail_2731_, v___x_2744_, v___x_2745_, v___x_2738_, v___y_2726_);
                    return v___x_2746_;
                }
            }
        } else {
            let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2750_: u8 = 0;
            v___x_2747_ = lean_nat_sub(v_start_2725_, v_tailOff_2733_);
            v___x_2748_ = lean_array_get_size(v_tail_2731_);
            v___x_2749_ = lean_box(0);
            v___x_2750_ = lean_nat_dec_lt(v___x_2747_, v___x_2748_);
            if v___x_2750_ == 0 {
                lean_dec(v___x_2747_);
                return v___x_2749_;
            } else {
                let mut v___x_2751_: u8 = 0;
                v___x_2751_ = lean_nat_dec_le(v___x_2748_, v___x_2748_);
                if v___x_2751_ == 0 {
                    if v___x_2750_ == 0 {
                        lean_dec(v___x_2747_);
                        return v___x_2749_;
                    } else {
                        let mut v___x_2752_: usize = 0;
                        let mut v___x_2753_: usize = 0;
                        let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2752_ = lean_usize_of_nat(v___x_2747_);
                        lean_dec(v___x_2747_);
                        v___x_2753_ = lean_usize_of_nat(v___x_2748_);
                        v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2723_, v_tail_2731_, v___x_2752_, v___x_2753_, v___x_2749_, v___y_2726_);
                        return v___x_2754_;
                    }
                } else {
                    let mut v___x_2755_: usize = 0;
                    let mut v___x_2756_: usize = 0;
                    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2755_ = lean_usize_of_nat(v___x_2747_);
                    lean_dec(v___x_2747_);
                    v___x_2756_ = lean_usize_of_nat(v___x_2748_);
                    v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2723_, v_tail_2731_, v___x_2755_, v___x_2756_, v___x_2749_, v___y_2726_);
                    return v___x_2757_;
                }
            }
        }
    } else {
        let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
        v___x_2758_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_2723_, v_t_2724_, v___y_2726_);
        return v___x_2758_;
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
    mut v_multigoals_2759_: *mut LeanObject,
    mut v_trees_2760_: *mut LeanObject,
    mut v_a_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2763_ = lean_unsigned_to_nat(0);
    v___x_2764_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_2759_, v_trees_2760_, v___x_2763_, v_a_2761_);
    return v___x_2764_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg___boxed(
    mut v_multigoals_2765_: *mut LeanObject,
    mut v_trees_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_a_2768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2769_: *mut LeanObject = core::ptr::null_mut();
    v_res_2769_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
        v_multigoals_2765_,
        v_trees_2766_,
        v_a_2767_,
    );
    lean_dec(v_a_2767_);
    lean_dec_ref(v_trees_2766_);
    lean_dec(v_multigoals_2765_);
    return v_res_2769_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg___boxed(
    mut v_multigoals_2770_: *mut LeanObject,
    mut v_as_2771_: *mut LeanObject,
    mut v_i_2772_: *mut LeanObject,
    mut v_stop_2773_: *mut LeanObject,
    mut v_b_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2777_: usize = 0;
    let mut v_stop_boxed_2778_: usize = 0;
    let mut v_res_2779_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2777_ = lean_unbox_usize(v_i_2772_);
    lean_dec(v_i_2772_);
    v_stop_boxed_2778_ = lean_unbox_usize(v_stop_2773_);
    lean_dec(v_stop_2773_);
    v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2770_, v_as_2771_, v_i_boxed_2777_, v_stop_boxed_2778_, v_b_2774_, v___y_2775_);
    lean_dec(v___y_2775_);
    lean_dec_ref(v_as_2771_);
    lean_dec(v_multigoals_2770_);
    return v_res_2779_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_multigoals_2780_: *mut LeanObject,
    mut v_as_2781_: *mut LeanObject,
    mut v_i_2782_: *mut LeanObject,
    mut v_stop_2783_: *mut LeanObject,
    mut v_b_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2787_: usize = 0;
    let mut v_stop_boxed_2788_: usize = 0;
    let mut v_res_2789_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2787_ = lean_unbox_usize(v_i_2782_);
    lean_dec(v_i_2782_);
    v_stop_boxed_2788_ = lean_unbox_usize(v_stop_2783_);
    lean_dec(v_stop_2783_);
    v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2780_, v_as_2781_, v_i_boxed_2787_, v_stop_boxed_2788_, v_b_2784_, v___y_2785_);
    lean_dec(v___y_2785_);
    lean_dec_ref(v_as_2781_);
    lean_dec(v_multigoals_2780_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg___boxed(
    mut v_multigoals_2790_: *mut LeanObject,
    mut v_t_2791_: *mut LeanObject,
    mut v___y_2792_: *mut LeanObject,
    mut v___y_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2794_: *mut LeanObject = core::ptr::null_mut();
    v_res_2794_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_2790_, v_t_2791_, v___y_2792_);
    lean_dec(v___y_2792_);
    lean_dec_ref(v_t_2791_);
    lean_dec(v_multigoals_2790_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_multigoals_2795_: *mut LeanObject,
    mut v_x_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2799_: *mut LeanObject = core::ptr::null_mut();
    v_res_2799_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_2795_, v_x_2796_, v___y_2797_);
    lean_dec(v___y_2797_);
    lean_dec_ref(v_x_2796_);
    lean_dec(v_multigoals_2795_);
    return v_res_2799_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg___boxed(
    mut v_multigoals_2800_: *mut LeanObject,
    mut v_t_2801_: *mut LeanObject,
    mut v_start_2802_: *mut LeanObject,
    mut v___y_2803_: *mut LeanObject,
    mut v___y_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2805_: *mut LeanObject = core::ptr::null_mut();
    v_res_2805_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_2800_, v_t_2801_, v_start_2802_, v___y_2803_);
    lean_dec(v___y_2803_);
    lean_dec(v_start_2802_);
    lean_dec_ref(v_t_2801_);
    lean_dec(v_multigoals_2800_);
    return v_res_2805_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg___boxed(
    mut v_multigoals_2806_: *mut LeanObject,
    mut v_x_2807_: *mut LeanObject,
    mut v_x_2808_: *mut LeanObject,
    mut v_x_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10205__boxed_2812_: usize = 0;
    let mut v_x_10206__boxed_2813_: usize = 0;
    let mut v_res_2814_: *mut LeanObject = core::ptr::null_mut();
    v_x_10205__boxed_2812_ = lean_unbox_usize(v_x_2808_);
    lean_dec(v_x_2808_);
    v_x_10206__boxed_2813_ = lean_unbox_usize(v_x_2809_);
    lean_dec(v_x_2809_);
    v_res_2814_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_2806_, v_x_2807_, v_x_10205__boxed_2812_, v_x_10206__boxed_2813_, v___y_2810_);
    lean_dec(v___y_2810_);
    lean_dec_ref(v_x_2807_);
    lean_dec(v_multigoals_2806_);
    return v_res_2814_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg___boxed(
    mut v_multigoals_2815_: *mut LeanObject,
    mut v_x_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2819_: *mut LeanObject = core::ptr::null_mut();
    v_res_2819_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(
        v_multigoals_2815_,
        v_x_2816_,
        v_a_2817_,
    );
    lean_dec(v_a_2817_);
    lean_dec(v_multigoals_2815_);
    return v_res_2819_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(
    mut v_multigoals_2820_: *mut LeanObject,
    mut v_00_u03c9_2821_: *mut LeanObject,
    mut v_trees_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    v___x_2825_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
        v_multigoals_2820_,
        v_trees_2822_,
        v_a_2823_,
    );
    return v___x_2825_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___boxed(
    mut v_multigoals_2826_: *mut LeanObject,
    mut v_00_u03c9_2827_: *mut LeanObject,
    mut v_trees_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList(
        v_multigoals_2826_,
        v_00_u03c9_2827_,
        v_trees_2828_,
        v_a_2829_,
    );
    lean_dec(v_a_2829_);
    lean_dec_ref(v_trees_2828_);
    lean_dec(v_multigoals_2826_);
    return v_res_2831_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(
    mut v_multigoals_2832_: *mut LeanObject,
    mut v_00_u03c9_2833_: *mut LeanObject,
    mut v_x_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    v___x_2837_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___redArg(
        v_multigoals_2832_,
        v_x_2834_,
        v_a_2835_,
    );
    return v___x_2837_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics___boxed(
    mut v_multigoals_2838_: *mut LeanObject,
    mut v_00_u03c9_2839_: *mut LeanObject,
    mut v_x_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2843_: *mut LeanObject = core::ptr::null_mut();
    v_res_2843_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics(
        v_multigoals_2838_,
        v_00_u03c9_2839_,
        v_x_2840_,
        v_a_2841_,
    );
    lean_dec(v_a_2841_);
    lean_dec(v_multigoals_2838_);
    return v_res_2843_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(
    mut v_00_u03c9_2844_: *mut LeanObject,
    mut v_multigoals_2845_: *mut LeanObject,
    mut v_t_2846_: *mut LeanObject,
    mut v_start_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    v___x_2850_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___redArg(v_multigoals_2845_, v_t_2846_, v_start_2847_, v___y_2848_);
    return v___x_2850_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0___boxed(
    mut v_00_u03c9_2851_: *mut LeanObject,
    mut v_multigoals_2852_: *mut LeanObject,
    mut v_t_2853_: *mut LeanObject,
    mut v_start_2854_: *mut LeanObject,
    mut v___y_2855_: *mut LeanObject,
    mut v___y_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2857_: *mut LeanObject = core::ptr::null_mut();
    v_res_2857_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0(v_00_u03c9_2851_, v_multigoals_2852_, v_t_2853_, v_start_2854_, v___y_2855_);
    lean_dec(v___y_2855_);
    lean_dec(v_start_2854_);
    lean_dec_ref(v_t_2853_);
    lean_dec(v_multigoals_2852_);
    return v_res_2857_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(
    mut v_00_u03b2_2858_: *mut LeanObject,
    mut v_m_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    v___x_2861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___redArg(v_m_2859_, v_a_2860_);
    return v___x_2861_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2___boxed(
    mut v_00_u03b2_2862_: *mut LeanObject,
    mut v_m_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2(v_00_u03b2_2862_, v_m_2863_, v_a_2864_);
    lean_dec_ref(v_a_2864_);
    lean_dec_ref(v_m_2863_);
    return v_res_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(
    mut v_00_u03b2_2866_: *mut LeanObject,
    mut v_m_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___redArg(v_m_2867_, v_a_2868_);
    return v___x_2869_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3___boxed(
    mut v_00_u03b2_2870_: *mut LeanObject,
    mut v_m_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2873_: *mut LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3(v_00_u03b2_2870_, v_m_2871_, v_a_2872_);
    lean_dec_ref(v_a_2872_);
    return v_res_2873_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4(
    mut v_00_u03b2_2874_: *mut LeanObject,
    mut v_m_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v_b_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4___redArg(v_m_2875_, v_a_2876_, v_b_2877_);
    return v___x_2878_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(
    mut v_00_u03c9_2879_: *mut LeanObject,
    mut v_multigoals_2880_: *mut LeanObject,
    mut v_x_2881_: *mut LeanObject,
    mut v_x_2882_: usize,
    mut v_x_2883_: usize,
    mut v___y_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    v___x_2886_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___redArg(v_multigoals_2880_, v_x_2881_, v_x_2882_, v_x_2883_, v___y_2884_);
    return v___x_2886_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0___boxed(
    mut v_00_u03c9_2887_: *mut LeanObject,
    mut v_multigoals_2888_: *mut LeanObject,
    mut v_x_2889_: *mut LeanObject,
    mut v_x_2890_: *mut LeanObject,
    mut v_x_2891_: *mut LeanObject,
    mut v___y_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10720__boxed_2894_: usize = 0;
    let mut v_x_10721__boxed_2895_: usize = 0;
    let mut v_res_2896_: *mut LeanObject = core::ptr::null_mut();
    v_x_10720__boxed_2894_ = lean_unbox_usize(v_x_2890_);
    lean_dec(v_x_2890_);
    v_x_10721__boxed_2895_ = lean_unbox_usize(v_x_2891_);
    lean_dec(v_x_2891_);
    v_res_2896_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0(v_00_u03c9_2887_, v_multigoals_2888_, v_x_2889_, v_x_10720__boxed_2894_, v_x_10721__boxed_2895_, v___y_2892_);
    lean_dec(v___y_2892_);
    lean_dec_ref(v_x_2889_);
    lean_dec(v_multigoals_2888_);
    return v_res_2896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(
    mut v_00_u03c9_2897_: *mut LeanObject,
    mut v_multigoals_2898_: *mut LeanObject,
    mut v_as_2899_: *mut LeanObject,
    mut v_i_2900_: usize,
    mut v_stop_2901_: usize,
    mut v_b_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___redArg(v_multigoals_2898_, v_as_2899_, v_i_2900_, v_stop_2901_, v_b_2902_, v___y_2903_);
    return v___x_2905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1___boxed(
    mut v_00_u03c9_2906_: *mut LeanObject,
    mut v_multigoals_2907_: *mut LeanObject,
    mut v_as_2908_: *mut LeanObject,
    mut v_i_2909_: *mut LeanObject,
    mut v_stop_2910_: *mut LeanObject,
    mut v_b_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2914_: usize = 0;
    let mut v_stop_boxed_2915_: usize = 0;
    let mut v_res_2916_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2914_ = lean_unbox_usize(v_i_2909_);
    lean_dec(v_i_2909_);
    v_stop_boxed_2915_ = lean_unbox_usize(v_stop_2910_);
    lean_dec(v_stop_2910_);
    v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__1(v_00_u03c9_2906_, v_multigoals_2907_, v_as_2908_, v_i_boxed_2914_, v_stop_boxed_2915_, v_b_2911_, v___y_2912_);
    lean_dec(v___y_2912_);
    lean_dec_ref(v_as_2908_);
    lean_dec(v_multigoals_2907_);
    return v_res_2916_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(
    mut v_00_u03c9_2917_: *mut LeanObject,
    mut v_multigoals_2918_: *mut LeanObject,
    mut v_t_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    v___x_2922_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___redArg(v_multigoals_2918_, v_t_2919_, v___y_2920_);
    return v___x_2922_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2___boxed(
    mut v_00_u03c9_2923_: *mut LeanObject,
    mut v_multigoals_2924_: *mut LeanObject,
    mut v_t_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2928_: *mut LeanObject = core::ptr::null_mut();
    v_res_2928_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__2(v_00_u03c9_2923_, v_multigoals_2924_, v_t_2925_, v___y_2926_);
    lean_dec(v___y_2926_);
    lean_dec_ref(v_t_2925_);
    lean_dec(v_multigoals_2924_);
    return v_res_2928_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(
    mut v_00_u03b2_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_x_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___redArg(v_a_2930_, v_x_2931_);
    return v___x_2932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5___boxed(
    mut v_00_u03b2_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_x_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2936_: *mut LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__2_spec__5(v_00_u03b2_2933_, v_a_2934_, v_x_2935_);
    lean_dec(v_x_2935_);
    lean_dec_ref(v_a_2934_);
    return v_res_2936_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(
    mut v_00_u03b2_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_x_2939_: *mut LeanObject,
) -> u8 {
    let mut v___x_2940_: u8 = 0;
    v___x_2940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___redArg(v_a_2938_, v_x_2939_);
    return v___x_2940_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7___boxed(
    mut v_00_u03b2_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_x_2943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2944_: u8 = 0;
    let mut v_r_2945_: *mut LeanObject = core::ptr::null_mut();
    v_res_2944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__7(v_00_u03b2_2941_, v_a_2942_, v_x_2943_);
    lean_dec(v_x_2943_);
    lean_dec_ref(v_a_2942_);
    v_r_2945_ = lean_box((v_res_2944_) as usize);
    return v_r_2945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(
    mut v_00_u03b2_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
    mut v_x_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___redArg(v_a_2947_, v_x_2948_);
    return v___x_2949_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8___boxed(
    mut v_00_u03b2_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_x_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__3_spec__8(v_00_u03b2_2950_, v_a_2951_, v_x_2952_);
    lean_dec_ref(v_a_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10(
    mut v_00_u03b2_2954_: *mut LeanObject,
    mut v_data_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10___redArg(v_data_2955_);
    return v___x_2956_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11(
    mut v_00_u03b2_2957_: *mut LeanObject,
    mut v_a_2958_: *mut LeanObject,
    mut v_b_2959_: *mut LeanObject,
    mut v_x_2960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__11___redArg(v_a_2958_, v_b_2959_, v_x_2960_);
    return v___x_2961_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(
    mut v_00_u03c9_2962_: *mut LeanObject,
    mut v_multigoals_2963_: *mut LeanObject,
    mut v_x_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___redArg(v_multigoals_2963_, v_x_2964_, v___y_2965_);
    return v___x_2967_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03c9_2968_: *mut LeanObject,
    mut v_multigoals_2969_: *mut LeanObject,
    mut v_x_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2973_: *mut LeanObject = core::ptr::null_mut();
    v_res_2973_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__2(v_00_u03c9_2968_, v_multigoals_2969_, v_x_2970_, v___y_2971_);
    lean_dec(v___y_2971_);
    lean_dec_ref(v_x_2970_);
    lean_dec(v_multigoals_2969_);
    return v_res_2973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(
    mut v_00_u03c9_2974_: *mut LeanObject,
    mut v_multigoals_2975_: *mut LeanObject,
    mut v_as_2976_: *mut LeanObject,
    mut v_i_2977_: usize,
    mut v_stop_2978_: usize,
    mut v_b_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___redArg(v_multigoals_2975_, v_as_2976_, v_i_2977_, v_stop_2978_, v_b_2979_, v___y_2980_);
    return v___x_2982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03c9_2983_: *mut LeanObject,
    mut v_multigoals_2984_: *mut LeanObject,
    mut v_as_2985_: *mut LeanObject,
    mut v_i_2986_: *mut LeanObject,
    mut v_stop_2987_: *mut LeanObject,
    mut v_b_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2991_: usize = 0;
    let mut v_stop_boxed_2992_: usize = 0;
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2991_ = lean_unbox_usize(v_i_2986_);
    lean_dec(v_i_2986_);
    v_stop_boxed_2992_ = lean_unbox_usize(v_stop_2987_);
    lean_dec(v_stop_2987_);
    v_res_2993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList_spec__0_spec__0_spec__3(v_00_u03c9_2983_, v_multigoals_2984_, v_as_2985_, v_i_boxed_2991_, v_stop_boxed_2992_, v_b_2988_, v___y_2989_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v_as_2985_);
    lean_dec(v_multigoals_2984_);
    return v_res_2993_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13(
    mut v_00_u03b2_2994_: *mut LeanObject,
    mut v_i_2995_: *mut LeanObject,
    mut v_source_2996_: *mut LeanObject,
    mut v_target_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    v___x_2998_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13___redArg(v_i_2995_, v_source_2996_, v_target_2997_);
    return v___x_2998_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14(
    mut v_00_u03b2_2999_: *mut LeanObject,
    mut v_x_3000_: *mut LeanObject,
    mut v_x_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTactics_spec__4_spec__10_spec__13_spec__14___redArg(v_x_3000_, v_x_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__0(
    mut v_a_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v___x_3004_ = lean_nat_to_int(v_a_3003_);
    return v___x_3004_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(
    mut v___y_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    v___x_3007_ = lean_st_ref_get(v___y_3005_);
    v_infoState_3008_ = lean_ctor_get(v___x_3007_, 8);
    lean_inc_ref(v_infoState_3008_);
    lean_dec(v___x_3007_);
    v_trees_3009_ = lean_ctor_get(v_infoState_3008_, 2);
    lean_inc_ref(v_trees_3009_);
    lean_dec_ref(v_infoState_3008_);
    v___x_3010_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3010_, 0, v_trees_3009_);
    return v___x_3010_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg___boxed(
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3013_: *mut LeanObject = core::ptr::null_mut();
    v_res_3013_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_3011_);
    lean_dec(v___y_3011_);
    return v_res_3013_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(
    mut v___y_3014_: *mut LeanObject,
    mut v___y_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_3015_);
    return v___x_3017_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___boxed(
    mut v___y_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3021_: *mut LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3(v___y_3018_, v___y_3019_);
    lean_dec(v___y_3019_);
    lean_dec_ref(v___y_3018_);
    return v_res_3021_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3022_ = lean_box(0);
    v___x_3023_ = lean_unsigned_to_nat(16);
    v___x_3024_ = lean_mk_array(v___x_3023_, v___x_3022_);
    return v___x_3024_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3025_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0_once), _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__0);
    v___x_3026_ = lean_unsigned_to_nat(0);
    v___x_3027_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3027_, 0, v___x_3026_);
    lean_ctor_set(v___x_3027_, 1, v___x_3025_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(
    mut v_stx_3028_: *mut LeanObject,
    mut v_val_3029_: *mut LeanObject,
    mut v_a_3030_: *mut LeanObject,
    mut v_x_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    v___x_3033_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1_once), _init_l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___closed__1);
    v___x_3034_ = lean_st_mk_ref(v___x_3033_);
    v___x_3035_ =
        l_Lean_Linter_Extra_UnnecessarySeqFocus_getTactics___redArg(v_stx_3028_, v___x_3034_);
    v___x_3036_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_markUsedTacticsList___redArg(
        v_val_3029_,
        v_a_3030_,
        v___x_3034_,
    );
    v___x_3037_ = lean_st_ref_get(v___x_3034_);
    lean_dec(v___x_3034_);
    v___x_3038_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3038_, 0, v___x_3036_);
    lean_ctor_set(v___x_3038_, 1, v___x_3037_);
    return v___x_3038_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed(
    mut v_stx_3039_: *mut LeanObject,
    mut v_val_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
    mut v_x_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0(
        v_stx_3039_,
        v_val_3040_,
        v_a_3041_,
        v_x_3042_,
    );
    lean_dec_ref(v_a_3041_);
    lean_dec(v_val_3040_);
    return v_res_3044_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(
    mut v_o_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    v___x_3048_ = lean_st_ref_get(v___y_3046_);
    v_env_3049_ = lean_ctor_get(v___x_3048_, 0);
    lean_inc_ref(v_env_3049_);
    lean_dec(v___x_3048_);
    v___x_3050_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_3051_ = lean_ctor_get(v___x_3050_, 0);
    v_asyncMode_3052_ = lean_ctor_get(v_toEnvExtension_3051_, 2);
    v___x_3053_ = lean_box(1);
    v___x_3054_ = lean_box(0);
    v_linterSets_3055_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_3053_,
        v___x_3050_,
        v_env_3049_,
        v_asyncMode_3052_,
        v___x_3054_,
    );
    v___x_3056_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3056_, 0, v_o_3045_);
    lean_ctor_set(v___x_3056_, 1, v_linterSets_3055_);
    v___x_3057_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3057_, 0, v___x_3056_);
    return v___x_3057_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg___boxed(
    mut v_o_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_3058_, v___y_3059_);
    lean_dec(v___y_3059_);
    return v_res_3061_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    v___x_3065_ = lean_st_ref_get(v___y_3063_);
    v_scopes_3066_ = lean_ctor_get(v___x_3065_, 2);
    lean_inc(v_scopes_3066_);
    lean_dec(v___x_3065_);
    v___x_3067_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3068_ = l_List_head_x21___redArg(v___x_3067_, v_scopes_3066_);
    lean_dec(v_scopes_3066_);
    v_opts_3069_ = lean_ctor_get(v___x_3068_, 1);
    lean_inc_ref(v_opts_3069_);
    lean_dec(v___x_3068_);
    v___x_3070_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_opts_3069_, v___y_3063_);
    return v___x_3070_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1___boxed(
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_3071_, v___y_3072_);
    lean_dec(v___y_3072_);
    lean_dec_ref(v___y_3071_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(
    mut v___y_3076_: u8,
    mut v_suppressElabErrors_3077_: u8,
    mut v_x_3078_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3078_) == 1 {
        let mut v_pre_3079_: *mut LeanObject = core::ptr::null_mut();
        v_pre_3079_ = lean_ctor_get(v_x_3078_, 0);
        if lean_obj_tag(v_pre_3079_) == 0 {
            let mut v_str_3080_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3082_: u8 = 0;
            v_str_3080_ = lean_ctor_get(v_x_3078_, 1);
            v___x_3081_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___closed__0;
            v___x_3082_ = lean_string_dec_eq(v_str_3080_, v___x_3081_);
            if v___x_3082_ == 0 {
                return v___y_3076_;
            } else {
                return v_suppressElabErrors_3077_;
            }
        } else {
            return v___y_3076_;
        }
    } else {
        return v___y_3076_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed(
    mut v___y_3083_: *mut LeanObject,
    mut v_suppressElabErrors_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8683__boxed_3086_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3087_: u8 = 0;
    let mut v_res_3088_: u8 = 0;
    let mut v_r_3089_: *mut LeanObject = core::ptr::null_mut();
    v___y_8683__boxed_3086_ = (lean_unbox(v___y_3083_) as u8);
    v_suppressElabErrors_boxed_3087_ = (lean_unbox(v_suppressElabErrors_3084_) as u8);
    v_res_3088_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0(v___y_8683__boxed_3086_, v_suppressElabErrors_boxed_3087_, v_x_3085_);
    lean_dec(v_x_3085_);
    v_r_3089_ = lean_box((v_res_3088_) as usize);
    return v_r_3089_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3090_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    v___x_3091_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__0);
    v___x_3092_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3092_, 0, v___x_3091_);
    return v___x_3092_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
    v___x_3094_ = lean_unsigned_to_nat(0);
    v___x_3095_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3095_, 0, v___x_3094_);
    lean_ctor_set(v___x_3095_, 1, v___x_3094_);
    lean_ctor_set(v___x_3095_, 2, v___x_3094_);
    lean_ctor_set(v___x_3095_, 3, v___x_3094_);
    lean_ctor_set(v___x_3095_, 4, v___x_3093_);
    lean_ctor_set(v___x_3095_, 5, v___x_3093_);
    lean_ctor_set(v___x_3095_, 6, v___x_3093_);
    lean_ctor_set(v___x_3095_, 7, v___x_3093_);
    lean_ctor_set(v___x_3095_, 8, v___x_3093_);
    lean_ctor_set(v___x_3095_, 9, v___x_3093_);
    return v___x_3095_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    v___x_3096_ = lean_unsigned_to_nat(32);
    v___x_3097_ = lean_mk_empty_array_with_capacity(v___x_3096_);
    v___x_3098_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3098_, 0, v___x_3097_);
    return v___x_3098_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3099_: usize = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    v___x_3099_ = 5usize;
    v___x_3100_ = lean_unsigned_to_nat(0);
    v___x_3101_ = lean_unsigned_to_nat(32);
    v___x_3102_ = lean_mk_empty_array_with_capacity(v___x_3101_);
    v___x_3103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__3);
    v___x_3104_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3104_, 0, v___x_3103_);
    lean_ctor_set(v___x_3104_, 1, v___x_3102_);
    lean_ctor_set(v___x_3104_, 2, v___x_3100_);
    lean_ctor_set(v___x_3104_, 3, v___x_3100_);
    lean_ctor_set_usize(v___x_3104_, 4, v___x_3099_);
    return v___x_3104_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3105_ = lean_box(1);
    v___x_3106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__4);
    v___x_3107_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__1);
    v___x_3108_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3108_, 0, v___x_3107_);
    lean_ctor_set(v___x_3108_, 1, v___x_3106_);
    lean_ctor_set(v___x_3108_, 2, v___x_3105_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(
    mut v_msgData_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    v___x_3112_ = lean_st_ref_get(v___y_3110_);
    v_env_3113_ = lean_ctor_get(v___x_3112_, 0);
    lean_inc_ref(v_env_3113_);
    lean_dec(v___x_3112_);
    v___x_3114_ = lean_st_ref_get(v___y_3110_);
    v_scopes_3115_ = lean_ctor_get(v___x_3114_, 2);
    lean_inc(v_scopes_3115_);
    lean_dec(v___x_3114_);
    v___x_3116_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3117_ = l_List_head_x21___redArg(v___x_3116_, v_scopes_3115_);
    lean_dec(v_scopes_3115_);
    v_opts_3118_ = lean_ctor_get(v___x_3117_, 1);
    lean_inc_ref(v_opts_3118_);
    lean_dec(v___x_3117_);
    v___x_3119_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__2);
    v___x_3120_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___closed__5);
    v___x_3121_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3121_, 0, v_env_3113_);
    lean_ctor_set(v___x_3121_, 1, v___x_3119_);
    lean_ctor_set(v___x_3121_, 2, v___x_3120_);
    lean_ctor_set(v___x_3121_, 3, v_opts_3118_);
    v___x_3122_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3122_, 0, v___x_3121_);
    lean_ctor_set(v___x_3122_, 1, v_msgData_3109_);
    v___x_3123_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3123_, 0, v___x_3122_);
    return v___x_3123_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg___boxed(
    mut v_msgData_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3127_: *mut LeanObject = core::ptr::null_mut();
    v_res_3127_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_3124_, v___y_3125_);
    lean_dec(v___y_3125_);
    return v_res_3127_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(
    mut v_opts_3128_: *mut LeanObject,
    mut v_opt_3129_: *mut LeanObject,
) -> u8 {
    let mut v_name_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v_name_3130_ = lean_ctor_get(v_opt_3129_, 0);
    v_defValue_3131_ = lean_ctor_get(v_opt_3129_, 1);
    v_map_3132_ = lean_ctor_get(v_opts_3128_, 0);
    v___x_3133_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3132_,
            v_name_3130_,
        );
    if lean_obj_tag(v___x_3133_) == 0 {
        let mut v___x_3134_: u8 = 0;
        v___x_3134_ = (lean_unbox(v_defValue_3131_) as u8);
        return v___x_3134_;
    } else {
        let mut v_val_3135_: *mut LeanObject = core::ptr::null_mut();
        v_val_3135_ = lean_ctor_get(v___x_3133_, 0);
        lean_inc(v_val_3135_);
        lean_dec_ref_known(v___x_3133_, 1);
        if lean_obj_tag(v_val_3135_) == 1 {
            let mut v_v_3136_: u8 = 0;
            v_v_3136_ = lean_ctor_get_uint8(v_val_3135_, 0 as u32);
            lean_dec_ref_known(v_val_3135_, 0);
            return v_v_3136_;
        } else {
            let mut v___x_3137_: u8 = 0;
            lean_dec(v_val_3135_);
            v___x_3137_ = (lean_unbox(v_defValue_3131_) as u8);
            return v___x_3137_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13___boxed(
    mut v_opts_3138_: *mut LeanObject,
    mut v_opt_3139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3140_: u8 = 0;
    let mut v_r_3141_: *mut LeanObject = core::ptr::null_mut();
    v_res_3140_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_3138_, v_opt_3139_);
    lean_dec_ref(v_opt_3139_);
    lean_dec_ref(v_opts_3138_);
    v_r_3141_ = lean_box((v_res_3140_) as usize);
    return v_r_3141_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(
    mut v_ref_3143_: *mut LeanObject,
    mut v_msgData_3144_: *mut LeanObject,
    mut v_severity_3145_: u8,
    mut v_isSilent_3146_: u8,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3151_: u8 = 0;
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: u8 = 0;
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v_isSharedCheck_3196_: u8 = 0;
    let mut v_a_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut v_a_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v___y_3214_: u8 = 0;
    let mut v___y_3215_: u8 = 0;
    let mut v___y_3216_: u8 = 0;
    let mut v___y_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3221_: u8 = 0;
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___y_3242_: u8 = 0;
    let mut v___y_3243_: u8 = 0;
    let mut v___y_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: u8 = 0;
    let mut v___y_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: u8 = 0;
    let mut v___y_3251_: u8 = 0;
    let mut v___y_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut v___x_3267_: u8 = 0;
    let mut v___y_3269_: u8 = 0;
    let mut v___y_3270_: u8 = 0;
    let mut v___y_3271_: u8 = 0;
    let mut v___y_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3267_ = 2;
                v___x_3285_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3145_, v___x_3267_);
                if v___x_3285_ == 0 {
                    v___y_3273_ = v___x_3285_;
                    state = 18;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_3144_);
                    v___x_3286_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3144_);
                    v___y_3273_ = v___x_3286_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_3159_ = l_Lean_Elab_Command_getScope___redArg(v___y_3158_);
                if lean_obj_tag(v___x_3159_) == 0 {
                    v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
                    lean_inc(v_a_3160_);
                    lean_dec_ref_known(v___x_3159_, 1);
                    v___x_3161_ = l_Lean_Elab_Command_getScope___redArg(v___y_3158_);
                    if lean_obj_tag(v___x_3161_) == 0 {
                        v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
                        v_isSharedCheck_3196_ = (!lean_is_exclusive(v___x_3161_)) as u8;
                        if v_isSharedCheck_3196_ == 0 {
                            v___x_3164_ = v___x_3161_;
                            v_isShared_3165_ = v_isSharedCheck_3196_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3162_);
                            lean_dec(v___x_3161_);
                            v___x_3164_ = lean_box(0);
                            v_isShared_3165_ = v_isSharedCheck_3196_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3160_);
                        lean_dec(v___y_3157_);
                        lean_dec_ref(v___y_3155_);
                        lean_dec_ref(v___y_3152_);
                        v_a_3197_ = lean_ctor_get(v___x_3161_, 0);
                        v_isSharedCheck_3204_ = (!lean_is_exclusive(v___x_3161_)) as u8;
                        if v_isSharedCheck_3204_ == 0 {
                            v___x_3199_ = v___x_3161_;
                            v_isShared_3200_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3197_);
                            lean_dec(v___x_3161_);
                            v___x_3199_ = lean_box(0);
                            v_isShared_3200_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3157_);
                    lean_dec_ref(v___y_3155_);
                    lean_dec_ref(v___y_3152_);
                    v_a_3205_ = lean_ctor_get(v___x_3159_, 0);
                    v_isSharedCheck_3212_ = (!lean_is_exclusive(v___x_3159_)) as u8;
                    if v_isSharedCheck_3212_ == 0 {
                        v___x_3207_ = v___x_3159_;
                        v_isShared_3208_ = v_isSharedCheck_3212_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3205_);
                        lean_dec(v___x_3159_);
                        v___x_3207_ = lean_box(0);
                        v_isShared_3208_ = v_isSharedCheck_3212_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3166_ = lean_st_ref_take(v___y_3158_);
                v_currNamespace_3167_ = lean_ctor_get(v_a_3160_, 2);
                lean_inc(v_currNamespace_3167_);
                lean_dec(v_a_3160_);
                v_openDecls_3168_ = lean_ctor_get(v_a_3162_, 3);
                lean_inc(v_openDecls_3168_);
                lean_dec(v_a_3162_);
                v_env_3169_ = lean_ctor_get(v___x_3166_, 0);
                v_messages_3170_ = lean_ctor_get(v___x_3166_, 1);
                v_scopes_3171_ = lean_ctor_get(v___x_3166_, 2);
                v_usedQuotCtxts_3172_ = lean_ctor_get(v___x_3166_, 3);
                v_nextMacroScope_3173_ = lean_ctor_get(v___x_3166_, 4);
                v_maxRecDepth_3174_ = lean_ctor_get(v___x_3166_, 5);
                v_ngen_3175_ = lean_ctor_get(v___x_3166_, 6);
                v_auxDeclNGen_3176_ = lean_ctor_get(v___x_3166_, 7);
                v_infoState_3177_ = lean_ctor_get(v___x_3166_, 8);
                v_traceState_3178_ = lean_ctor_get(v___x_3166_, 9);
                v_snapshotTasks_3179_ = lean_ctor_get(v___x_3166_, 10);
                v_isSharedCheck_3195_ = (!lean_is_exclusive(v___x_3166_)) as u8;
                if v_isSharedCheck_3195_ == 0 {
                    v___x_3181_ = v___x_3166_;
                    v_isShared_3182_ = v_isSharedCheck_3195_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3179_);
                    lean_inc(v_traceState_3178_);
                    lean_inc(v_infoState_3177_);
                    lean_inc(v_auxDeclNGen_3176_);
                    lean_inc(v_ngen_3175_);
                    lean_inc(v_maxRecDepth_3174_);
                    lean_inc(v_nextMacroScope_3173_);
                    lean_inc(v_usedQuotCtxts_3172_);
                    lean_inc(v_scopes_3171_);
                    lean_inc(v_messages_3170_);
                    lean_inc(v_env_3169_);
                    lean_dec(v___x_3166_);
                    v___x_3181_ = lean_box(0);
                    v_isShared_3182_ = v_isSharedCheck_3195_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3183_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3183_, 0, v_currNamespace_3167_);
                lean_ctor_set(v___x_3183_, 1, v_openDecls_3168_);
                v___x_3184_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3184_, 0, v___x_3183_);
                lean_ctor_set(v___x_3184_, 1, v___y_3155_);
                lean_inc_ref(v___y_3153_);
                lean_inc_ref(v___y_3154_);
                v___x_3185_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_3185_, 0, v___y_3154_);
                lean_ctor_set(v___x_3185_, 1, v___y_3152_);
                lean_ctor_set(v___x_3185_, 2, v___y_3157_);
                lean_ctor_set(v___x_3185_, 3, v___y_3153_);
                lean_ctor_set(v___x_3185_, 4, v___x_3184_);
                lean_ctor_set_uint8(
                    v___x_3185_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3151_,
                );
                lean_ctor_set_uint8(
                    v___x_3185_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_3156_,
                );
                lean_ctor_set_uint8(
                    v___x_3185_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3146_,
                );
                v___x_3186_ = l_Lean_MessageLog_add(v___x_3185_, v_messages_3170_);
                if v_isShared_3182_ == 0 {
                    lean_ctor_set(v___x_3181_, 1, v___x_3186_);
                    v___x_3188_ = v___x_3181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_env_3169_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3186_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_scopes_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_usedQuotCtxts_3172_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 4, v_nextMacroScope_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 5, v_maxRecDepth_3174_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 6, v_ngen_3175_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 7, v_auxDeclNGen_3176_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 8, v_infoState_3177_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 9, v_traceState_3178_);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 10, v_snapshotTasks_3179_);
                    v___x_3188_ = v_reuseFailAlloc_3194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3189_ = lean_st_ref_set(v___y_3158_, v___x_3188_);
                v___x_3190_ = lean_box(0);
                if v_isShared_3165_ == 0 {
                    lean_ctor_set(v___x_3164_, 0, v___x_3190_);
                    v___x_3192_ = v___x_3164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3192_;
            }
            6 => {
                if v_isShared_3200_ == 0 {
                    v___x_3202_ = v___x_3199_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3202_;
            }
            8 => {
                if v_isShared_3208_ == 0 {
                    v___x_3210_ = v___x_3207_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3210_;
            }
            10 => {
                v_fileName_3219_ = lean_ctor_get(v___y_3147_, 0);
                v_fileMap_3220_ = lean_ctor_get(v___y_3147_, 1);
                v_suppressElabErrors_3221_ = lean_ctor_get_uint8(
                    v___y_3147_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_3222_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3144_,
                    );
                v___x_3223_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v___x_3222_, v___y_3148_);
                v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
                v_isSharedCheck_3240_ = (!lean_is_exclusive(v___x_3223_)) as u8;
                if v_isSharedCheck_3240_ == 0 {
                    v___x_3226_ = v___x_3223_;
                    v_isShared_3227_ = v_isSharedCheck_3240_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_3224_);
                    lean_dec(v___x_3223_);
                    v___x_3226_ = lean_box(0);
                    v_isShared_3227_ = v_isSharedCheck_3240_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_3220_, 2);
                v___x_3228_ = l_Lean_FileMap_toPosition(v_fileMap_3220_, v___y_3217_);
                lean_dec(v___y_3217_);
                v___x_3229_ = l_Lean_FileMap_toPosition(v_fileMap_3220_, v___y_3218_);
                lean_dec(v___y_3218_);
                v___x_3230_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3230_, 0, v___x_3229_);
                v___x_3231_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___closed__0;
                if v_suppressElabErrors_3221_ == 0 {
                    lean_del_object(v___x_3226_);
                    v___y_3151_ = v___y_3215_;
                    v___y_3152_ = v___x_3228_;
                    v___y_3153_ = v___x_3231_;
                    v___y_3154_ = v_fileName_3219_;
                    v___y_3155_ = v_a_3224_;
                    v___y_3156_ = v___y_3216_;
                    v___y_3157_ = v___x_3230_;
                    v___y_3158_ = v___y_3148_;
                    state = 1;
                    continue;
                } else {
                    v___x_3232_ = lean_box((v___y_3214_) as usize);
                    v___x_3233_ = lean_box((v_suppressElabErrors_3221_) as usize);
                    v___f_3234_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_3234_, 0, v___x_3232_);
                    lean_closure_set(v___f_3234_, 1, v___x_3233_);
                    lean_inc(v_a_3224_);
                    v___x_3235_ = l_Lean_MessageData_hasTag(v___f_3234_, v_a_3224_);
                    if v___x_3235_ == 0 {
                        lean_dec_ref_known(v___x_3230_, 1);
                        lean_dec_ref(v___x_3228_);
                        lean_dec(v_a_3224_);
                        v___x_3236_ = lean_box(0);
                        if v_isShared_3227_ == 0 {
                            lean_ctor_set(v___x_3226_, 0, v___x_3236_);
                            v___x_3238_ = v___x_3226_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
                            v___x_3238_ = v_reuseFailAlloc_3239_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3226_);
                        v___y_3151_ = v___y_3215_;
                        v___y_3152_ = v___x_3228_;
                        v___y_3153_ = v___x_3231_;
                        v___y_3154_ = v_fileName_3219_;
                        v___y_3155_ = v_a_3224_;
                        v___y_3156_ = v___y_3216_;
                        v___y_3157_ = v___x_3230_;
                        v___y_3158_ = v___y_3148_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_3238_;
            }
            13 => {
                v___x_3247_ = l_Lean_Syntax_getTailPos_x3f(v___y_3244_, v___y_3243_);
                lean_dec(v___y_3244_);
                if lean_obj_tag(v___x_3247_) == 0 {
                    lean_inc(v___y_3246_);
                    v___y_3214_ = v___y_3242_;
                    v___y_3215_ = v___y_3243_;
                    v___y_3216_ = v___y_3245_;
                    v___y_3217_ = v___y_3246_;
                    v___y_3218_ = v___y_3246_;
                    state = 10;
                    continue;
                } else {
                    v_val_3248_ = lean_ctor_get(v___x_3247_, 0);
                    lean_inc(v_val_3248_);
                    lean_dec_ref_known(v___x_3247_, 1);
                    v___y_3214_ = v___y_3242_;
                    v___y_3215_ = v___y_3243_;
                    v___y_3216_ = v___y_3245_;
                    v___y_3217_ = v___y_3246_;
                    v___y_3218_ = v_val_3248_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_3253_ = l_Lean_Elab_Command_getRef___redArg(v___y_3147_);
                if lean_obj_tag(v___x_3253_) == 0 {
                    v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
                    lean_inc(v_a_3254_);
                    lean_dec_ref_known(v___x_3253_, 1);
                    v_ref_3255_ = l_Lean_replaceRef(v_ref_3143_, v_a_3254_);
                    lean_dec(v_a_3254_);
                    v___x_3256_ = l_Lean_Syntax_getPos_x3f(v_ref_3255_, v___y_3251_);
                    if lean_obj_tag(v___x_3256_) == 0 {
                        v___x_3257_ = lean_unsigned_to_nat(0);
                        v___y_3242_ = v___y_3250_;
                        v___y_3243_ = v___y_3251_;
                        v___y_3244_ = v_ref_3255_;
                        v___y_3245_ = v___y_3252_;
                        v___y_3246_ = v___x_3257_;
                        state = 13;
                        continue;
                    } else {
                        v_val_3258_ = lean_ctor_get(v___x_3256_, 0);
                        lean_inc(v_val_3258_);
                        lean_dec_ref_known(v___x_3256_, 1);
                        v___y_3242_ = v___y_3250_;
                        v___y_3243_ = v___y_3251_;
                        v___y_3244_ = v_ref_3255_;
                        v___y_3245_ = v___y_3252_;
                        v___y_3246_ = v_val_3258_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_3144_);
                    v_a_3259_ = lean_ctor_get(v___x_3253_, 0);
                    v_isSharedCheck_3266_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3261_ = v___x_3253_;
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3259_);
                        lean_dec(v___x_3253_);
                        v___x_3261_ = lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_3262_ == 0 {
                    v___x_3264_ = v___x_3261_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
                    v___x_3264_ = v_reuseFailAlloc_3265_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3264_;
            }
            17 => {
                if v___y_3271_ == 0 {
                    v___y_3250_ = v___y_3269_;
                    v___y_3251_ = v___y_3270_;
                    v___y_3252_ = v_severity_3145_;
                    state = 14;
                    continue;
                } else {
                    v___y_3250_ = v___y_3269_;
                    v___y_3251_ = v___y_3270_;
                    v___y_3252_ = v___x_3267_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_3273_ == 0 {
                    v___x_3274_ = lean_st_ref_get(v___y_3148_);
                    v_scopes_3275_ = lean_ctor_get(v___x_3274_, 2);
                    lean_inc(v_scopes_3275_);
                    lean_dec(v___x_3274_);
                    v___x_3276_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3277_ = l_List_head_x21___redArg(v___x_3276_, v_scopes_3275_);
                    lean_dec(v_scopes_3275_);
                    v_opts_3278_ = lean_ctor_get(v___x_3277_, 1);
                    lean_inc_ref(v_opts_3278_);
                    lean_dec(v___x_3277_);
                    v___x_3279_ = 1;
                    v___x_3280_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3145_, v___x_3279_);
                    if v___x_3280_ == 0 {
                        lean_dec_ref(v_opts_3278_);
                        v___y_3269_ = v___y_3273_;
                        v___y_3270_ = v___y_3273_;
                        v___y_3271_ = v___x_3280_;
                        state = 17;
                        continue;
                    } else {
                        v___x_3281_ = l_Lean_warningAsError;
                        v___x_3282_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__13(v_opts_3278_, v___x_3281_);
                        lean_dec_ref(v_opts_3278_);
                        v___y_3269_ = v___y_3273_;
                        v___y_3270_ = v___y_3273_;
                        v___y_3271_ = v___x_3282_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_3144_);
                    v___x_3283_ = lean_box(0);
                    v___x_3284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3284_, 0, v___x_3283_);
                    return v___x_3284_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10___boxed(
    mut v_ref_3287_: *mut LeanObject,
    mut v_msgData_3288_: *mut LeanObject,
    mut v_severity_3289_: *mut LeanObject,
    mut v_isSilent_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3294_: u8 = 0;
    let mut v_isSilent_boxed_3295_: u8 = 0;
    let mut v_res_3296_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3294_ = (lean_unbox(v_severity_3289_) as u8);
    v_isSilent_boxed_3295_ = (lean_unbox(v_isSilent_3290_) as u8);
    v_res_3296_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_3287_, v_msgData_3288_, v_severity_boxed_3294_, v_isSilent_boxed_3295_, v___y_3291_, v___y_3292_);
    lean_dec(v___y_3292_);
    lean_dec_ref(v___y_3291_);
    lean_dec(v_ref_3287_);
    return v_res_3296_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(
    mut v_ref_3297_: *mut LeanObject,
    mut v_msgData_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3302_: u8 = 0;
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    v___x_3302_ = 1;
    v___x_3303_ = 0;
    v___x_3304_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10(v_ref_3297_, v_msgData_3298_, v___x_3302_, v___x_3303_, v___y_3299_, v___y_3300_);
    return v___x_3304_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5___boxed(
    mut v_ref_3305_: *mut LeanObject,
    mut v_msgData_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3310_: *mut LeanObject = core::ptr::null_mut();
    v_res_3310_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_ref_3305_, v_msgData_3306_, v___y_3307_, v___y_3308_);
    lean_dec(v___y_3308_);
    lean_dec_ref(v___y_3307_);
    lean_dec(v_ref_3305_);
    return v_res_3310_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3312_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__0;
    v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
    return v___x_3313_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    v___x_3315_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__2;
    v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
    return v___x_3316_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(
    mut v_linterOption_3317_: *mut LeanObject,
    mut v_stx_3318_: *mut LeanObject,
    mut v_msg_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_unused_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3323_ = lean_ctor_get(v_linterOption_3317_, 0);
                v_isSharedCheck_3340_ = (!lean_is_exclusive(v_linterOption_3317_)) as u8;
                if v_isSharedCheck_3340_ == 0 {
                    v_unused_3341_ = lean_ctor_get(v_linterOption_3317_, 1);
                    lean_dec(v_unused_3341_);
                    v___x_3325_ = v_linterOption_3317_;
                    v_isShared_3326_ = v_isSharedCheck_3340_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_3323_);
                    lean_dec(v_linterOption_3317_);
                    v___x_3325_ = lean_box(0);
                    v_isShared_3326_ = v_isSharedCheck_3340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3327_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__1);
                lean_inc(v_name_3323_);
                v___x_3328_ = l_Lean_MessageData_ofName(v_name_3323_);
                if v_isShared_3326_ == 0 {
                    lean_ctor_set_tag(v___x_3325_, 7);
                    lean_ctor_set(v___x_3325_, 1, v___x_3328_);
                    lean_ctor_set(v___x_3325_, 0, v___x_3327_);
                    v___x_3330_ = v___x_3325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3327_);
                    lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3328_);
                    v___x_3330_ = v_reuseFailAlloc_3339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3331_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___closed__3);
                v___x_3332_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3332_, 0, v___x_3330_);
                lean_ctor_set(v___x_3332_, 1, v___x_3331_);
                v_disable_3333_ = l_Lean_MessageData_note(v___x_3332_);
                v___x_3334_ = l_Lean_Linter_linterMessageTag;
                v___x_3335_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3335_, 0, v_msg_3319_);
                lean_ctor_set(v___x_3335_, 1, v_disable_3333_);
                v___x_3336_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3336_, 0, v___x_3334_);
                lean_ctor_set(v___x_3336_, 1, v___x_3335_);
                v___x_3337_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3337_, 0, v_name_3323_);
                lean_ctor_set(v___x_3337_, 1, v___x_3336_);
                v___x_3338_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5(v_stx_3318_, v___x_3337_, v___y_3320_, v___y_3321_);
                return v___x_3338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3___boxed(
    mut v_linterOption_3342_: *mut LeanObject,
    mut v_stx_3343_: *mut LeanObject,
    mut v_msg_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3348_: *mut LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_3342_, v_stx_3343_, v_msg_3344_, v___y_3345_, v___y_3346_);
    lean_dec(v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec(v_stx_3343_);
    return v_res_3348_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(
    mut v_linterOption_3349_: *mut LeanObject,
    mut v_stx_3350_: *mut LeanObject,
    mut v_msg_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3355_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_3352_, v___y_3353_);
                v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
                v_isSharedCheck_3366_ = (!lean_is_exclusive(v___x_3355_)) as u8;
                if v_isSharedCheck_3366_ == 0 {
                    v___x_3358_ = v___x_3355_;
                    v_isShared_3359_ = v_isSharedCheck_3366_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3356_);
                    lean_dec(v___x_3355_);
                    v___x_3358_ = lean_box(0);
                    v_isShared_3359_ = v_isSharedCheck_3366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3360_ = l_Lean_Linter_getLinterValueExtra(v_linterOption_3349_, v_a_3356_);
                lean_dec(v_a_3356_);
                if v___x_3360_ == 0 {
                    lean_dec_ref(v_msg_3351_);
                    lean_dec_ref(v_linterOption_3349_);
                    v___x_3361_ = lean_box(0);
                    if v_isShared_3359_ == 0 {
                        lean_ctor_set(v___x_3358_, 0, v___x_3361_);
                        v___x_3363_ = v___x_3358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
                        v___x_3363_ = v_reuseFailAlloc_3364_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3358_);
                    v___x_3365_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3(v_linterOption_3349_, v_stx_3350_, v_msg_3351_, v___y_3352_, v___y_3353_);
                    return v___x_3365_;
                }
            }
            2 => {
                return v___x_3363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2___boxed(
    mut v_linterOption_3367_: *mut LeanObject,
    mut v_stx_3368_: *mut LeanObject,
    mut v_msg_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v_linterOption_3367_, v_stx_3368_, v_msg_3369_, v___y_3370_, v___y_3371_);
    lean_dec(v___y_3371_);
    lean_dec_ref(v___y_3370_);
    lean_dec(v_stx_3368_);
    return v_res_3373_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__1;
    v___x_3378_ = l_Lean_MessageData_ofFormat(v___x_3377_);
    return v___x_3378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(
    mut v_as_3379_: *mut LeanObject,
    mut v_sz_3380_: usize,
    mut v_i_3381_: usize,
    mut v_b_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: usize = 0;
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3412_: u8 = 0;
    let mut v___x_3413_: u8 = 0;
    let mut v___x_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3391_ = lean_usize_dec_lt(v_i_3381_, v_sz_3380_);
                if v___x_3391_ == 0 {
                    v___x_3392_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3392_, 0, v_b_3382_);
                    return v___x_3392_;
                } else {
                    v_a_3393_ = lean_array_uget_borrowed(v_as_3379_, v_i_3381_);
                    v_fst_3394_ = lean_ctor_get(v_a_3393_, 0);
                    v_snd_3395_ = lean_ctor_get(v_a_3393_, 1);
                    v_start_3396_ = lean_ctor_get(v_b_3382_, 0);
                    v_stop_3397_ = lean_ctor_get(v_b_3382_, 1);
                    v_start_3398_ = lean_ctor_get(v_fst_3394_, 0);
                    v_stop_3399_ = lean_ctor_get(v_fst_3394_, 1);
                    v___x_3400_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
                    v___x_3413_ = lean_nat_dec_le(v_start_3396_, v_start_3398_);
                    if v___x_3413_ == 0 {
                        v___y_3402_ = v___x_3413_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3414_ = lean_nat_dec_le(v_stop_3399_, v_stop_3397_);
                        v___y_3402_ = v___x_3414_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3388_ = 1usize;
                v___x_3389_ = lean_usize_add(v_i_3381_, v___x_3388_);
                v_i_3381_ = v___x_3389_;
                v_b_3382_ = v_a_3387_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3402_ == 0 {
                    lean_dec_ref(v_b_3382_);
                    v___x_3403_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___closed__2);
                    v___x_3404_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2(v___x_3400_, v_snd_3395_, v___x_3403_, v___y_3383_, v___y_3384_);
                    if lean_obj_tag(v___x_3404_) == 0 {
                        lean_dec_ref_known(v___x_3404_, 1);
                        lean_inc(v_fst_3394_);
                        v_a_3387_ = v_fst_3394_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
                        v_isSharedCheck_3412_ = (!lean_is_exclusive(v___x_3404_)) as u8;
                        if v_isSharedCheck_3412_ == 0 {
                            v___x_3407_ = v___x_3404_;
                            v_isShared_3408_ = v_isSharedCheck_3412_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3405_);
                            lean_dec(v___x_3404_);
                            v___x_3407_ = lean_box(0);
                            v_isShared_3408_ = v_isSharedCheck_3412_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3387_ = v_b_3382_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3408_ == 0 {
                    v___x_3410_ = v___x_3407_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
                    v___x_3410_ = v_reuseFailAlloc_3411_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4___boxed(
    mut v_as_3415_: *mut LeanObject,
    mut v_sz_3416_: *mut LeanObject,
    mut v_i_3417_: *mut LeanObject,
    mut v_b_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3422_: usize = 0;
    let mut v_i_boxed_3423_: usize = 0;
    let mut v_res_3424_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3416_);
    lean_dec(v_sz_3416_);
    v_i_boxed_3423_ = lean_unbox_usize(v_i_3417_);
    lean_dec(v_i_3417_);
    v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v_as_3415_, v_sz_boxed_3422_, v_i_boxed_3423_, v_b_3418_, v___y_3419_, v___y_3420_);
    lean_dec(v___y_3420_);
    lean_dec_ref(v___y_3419_);
    lean_dec_ref(v_as_3415_);
    return v_res_3424_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(
    mut v_r_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_3426_ = lean_ctor_get(v_r_3425_, 0);
                v_stop_3427_ = lean_ctor_get(v_r_3425_, 1);
                v_isSharedCheck_3436_ = (!lean_is_exclusive(v_r_3425_)) as u8;
                if v_isSharedCheck_3436_ == 0 {
                    v___x_3429_ = v_r_3425_;
                    v_isShared_3430_ = v_isSharedCheck_3436_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_3427_);
                    lean_inc(v_start_3426_);
                    lean_dec(v_r_3425_);
                    v___x_3429_ = lean_box(0);
                    v_isShared_3430_ = v_isSharedCheck_3436_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3431_ = lean_nat_to_int(v_stop_3427_);
                v___x_3432_ = lean_int_neg(v___x_3431_);
                lean_dec(v___x_3431_);
                if v_isShared_3430_ == 0 {
                    lean_ctor_set(v___x_3429_, 1, v___x_3432_);
                    v___x_3434_ = v___x_3429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_start_3426_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3432_);
                    v___x_3434_ = v_reuseFailAlloc_3435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(
    mut v_hi_3439_: *mut LeanObject,
    mut v_pivot_3440_: *mut LeanObject,
    mut v_as_3441_: *mut LeanObject,
    mut v_i_3442_: *mut LeanObject,
    mut v_k_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8369__overap_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3448_ = lean_nat_dec_lt(v_k_3443_, v_hi_3439_);
                if v___x_3448_ == 0 {
                    lean_dec(v_k_3443_);
                    lean_dec_ref(v_pivot_3440_);
                    v___x_3449_ = lean_array_fswap(v_as_3441_, v_i_3442_, v_hi_3439_);
                    v___x_3450_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3450_, 0, v_i_3442_);
                    lean_ctor_set(v___x_3450_, 1, v___x_3449_);
                    return v___x_3450_;
                } else {
                    v___x_3451_ = lean_array_fget_borrowed(v_as_3441_, v_k_3443_);
                    v_fst_3452_ = lean_ctor_get(v___x_3451_, 0);
                    v_fst_3453_ = lean_ctor_get(v_pivot_3440_, 0);
                    v___f_3454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0;
                    v___f_3455_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1;
                    lean_inc(v_fst_3452_);
                    v___x_3456_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_3452_);
                    lean_inc(v_fst_3453_);
                    v___x_3457_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__0(v_fst_3453_);
                    v___x_8369__overap_3458_ = l_lexOrd___redArg(v___f_3454_, v___f_3455_);
                    v___x_3459_ = lean_apply_2(v___x_8369__overap_3458_, v___x_3456_, v___x_3457_);
                    v___x_3460_ = (lean_unbox(v___x_3459_) as u8);
                    if v___x_3460_ == 0 {
                        if v___x_3448_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3461_ = lean_array_fswap(v_as_3441_, v_i_3442_, v_k_3443_);
                            v___x_3462_ = lean_unsigned_to_nat(1);
                            v___x_3463_ = lean_nat_add(v_i_3442_, v___x_3462_);
                            lean_dec(v_i_3442_);
                            v___x_3464_ = lean_nat_add(v_k_3443_, v___x_3462_);
                            lean_dec(v_k_3443_);
                            v_as_3441_ = v___x_3461_;
                            v_i_3442_ = v___x_3463_;
                            v_k_3443_ = v___x_3464_;
                            state = 0;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3445_ = lean_unsigned_to_nat(1);
                v___x_3446_ = lean_nat_add(v_k_3443_, v___x_3445_);
                lean_dec(v_k_3443_);
                v_k_3443_ = v___x_3446_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___boxed(
    mut v_hi_3466_: *mut LeanObject,
    mut v_pivot_3467_: *mut LeanObject,
    mut v_as_3468_: *mut LeanObject,
    mut v_i_3469_: *mut LeanObject,
    mut v_k_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3471_: *mut LeanObject = core::ptr::null_mut();
    v_res_3471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_3466_, v_pivot_3467_, v_as_3468_, v_i_3469_, v_k_3470_);
    lean_dec(v_hi_3466_);
    return v_res_3471_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(
    mut v___f_3472_: *mut LeanObject,
    mut v___x_3473_: u8,
    mut v_x1_3474_: *mut LeanObject,
    mut v_x2_3475_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568__overap_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: u8 = 0;
    v_fst_3476_ = lean_ctor_get(v_x1_3474_, 0);
    lean_inc(v_fst_3476_);
    lean_dec_ref(v_x1_3474_);
    v_fst_3477_ = lean_ctor_get(v_x2_3475_, 0);
    lean_inc(v_fst_3477_);
    lean_dec_ref(v_x2_3475_);
    v___f_3478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__0;
    v___f_3479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg___closed__1;
    lean_inc_ref(v___f_3472_);
    v___x_3480_ = lean_apply_1(v___f_3472_, v_fst_3476_);
    v___x_3481_ = lean_apply_1(v___f_3472_, v_fst_3477_);
    v___x_8568__overap_3482_ = l_lexOrd___redArg(v___f_3478_, v___f_3479_);
    v___x_3483_ = lean_apply_2(v___x_8568__overap_3482_, v___x_3480_, v___x_3481_);
    v___x_3484_ = (lean_unbox(v___x_3483_) as u8);
    if v___x_3484_ == 0 {
        return v___x_3473_;
    } else {
        let mut v___x_3485_: u8 = 0;
        v___x_3485_ = 0;
        return v___x_3485_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1___boxed(
    mut v___f_3486_: *mut LeanObject,
    mut v___x_3487_: *mut LeanObject,
    mut v_x1_3488_: *mut LeanObject,
    mut v_x2_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9308__boxed_3490_: u8 = 0;
    let mut v_res_3491_: u8 = 0;
    let mut v_r_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_9308__boxed_3490_ = (lean_unbox(v___x_3487_) as u8);
    v_res_3491_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_3486_, v___x_9308__boxed_3490_, v_x1_3488_, v_x2_3489_);
    v_r_3492_ = lean_box((v_res_3491_) as usize);
    return v_r_3492_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(
    mut v_n_3494_: *mut LeanObject,
    mut v_as_3495_: *mut LeanObject,
    mut v_lo_3496_: *mut LeanObject,
    mut v_hi_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: u8 = 0;
    let mut v___f_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: u8 = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3509_ = lean_nat_dec_lt(v_lo_3496_, v_hi_3497_);
                if v___x_3509_ == 0 {
                    lean_dec(v_lo_3496_);
                    return v_as_3495_;
                } else {
                    v___f_3510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___closed__0;
                    v___x_3511_ = lean_nat_add(v_lo_3496_, v_hi_3497_);
                    v___x_3512_ = lean_unsigned_to_nat(1);
                    v_mid_3513_ = lean_nat_shiftr(v___x_3511_, v___x_3512_);
                    lean_dec(v___x_3511_);
                    v___x_3526_ = lean_array_fget_borrowed(v_as_3495_, v_mid_3513_);
                    v___x_3527_ = lean_array_fget_borrowed(v_as_3495_, v_lo_3496_);
                    lean_inc(v___x_3527_);
                    lean_inc(v___x_3526_);
                    v___x_3528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_3510_, v___x_3509_, v___x_3526_, v___x_3527_);
                    if v___x_3528_ == 0 {
                        v___y_3521_ = v_as_3495_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3529_ = lean_array_fswap(v_as_3495_, v_lo_3496_, v_mid_3513_);
                        v___y_3521_ = v___x_3529_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3500_ = lean_array_fget(v___y_3499_, v_hi_3497_);
                lean_inc_n(v_lo_3496_, 2);
                v___x_3501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_3497_, v_pivot_3500_, v___y_3499_, v_lo_3496_, v_lo_3496_);
                v_fst_3502_ = lean_ctor_get(v___x_3501_, 0);
                lean_inc(v_fst_3502_);
                v_snd_3503_ = lean_ctor_get(v___x_3501_, 1);
                lean_inc(v_snd_3503_);
                lean_dec_ref(v___x_3501_);
                v___x_3504_ = lean_nat_dec_le(v_hi_3497_, v_fst_3502_);
                if v___x_3504_ == 0 {
                    v___x_3505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_3494_, v_snd_3503_, v_lo_3496_, v_fst_3502_);
                    v___x_3506_ = lean_unsigned_to_nat(1);
                    v___x_3507_ = lean_nat_add(v_fst_3502_, v___x_3506_);
                    lean_dec(v_fst_3502_);
                    v_as_3495_ = v___x_3505_;
                    v_lo_3496_ = v___x_3507_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_3502_);
                    lean_dec(v_lo_3496_);
                    return v_snd_3503_;
                }
            }
            2 => {
                v___x_3516_ = lean_array_fget_borrowed(v___y_3515_, v_mid_3513_);
                v___x_3517_ = lean_array_fget_borrowed(v___y_3515_, v_hi_3497_);
                lean_inc(v___x_3517_);
                lean_inc(v___x_3516_);
                v___x_3518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_3510_, v___x_3509_, v___x_3516_, v___x_3517_);
                if v___x_3518_ == 0 {
                    lean_dec(v_mid_3513_);
                    v___y_3499_ = v___y_3515_;
                    state = 1;
                    continue;
                } else {
                    v___x_3519_ = lean_array_fswap(v___y_3515_, v_mid_3513_, v_hi_3497_);
                    lean_dec(v_mid_3513_);
                    v___y_3499_ = v___x_3519_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3522_ = lean_array_fget_borrowed(v___y_3521_, v_hi_3497_);
                v___x_3523_ = lean_array_fget_borrowed(v___y_3521_, v_lo_3496_);
                lean_inc(v___x_3523_);
                lean_inc(v___x_3522_);
                v___x_3524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___lam__1(v___f_3510_, v___x_3509_, v___x_3522_, v___x_3523_);
                if v___x_3524_ == 0 {
                    v___y_3515_ = v___y_3521_;
                    state = 2;
                    continue;
                } else {
                    v___x_3525_ = lean_array_fswap(v___y_3521_, v_lo_3496_, v_hi_3497_);
                    v___y_3515_ = v___x_3525_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg___boxed(
    mut v_n_3530_: *mut LeanObject,
    mut v_as_3531_: *mut LeanObject,
    mut v_lo_3532_: *mut LeanObject,
    mut v_hi_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3534_: *mut LeanObject = core::ptr::null_mut();
    v_res_3534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_3530_, v_as_3531_, v_lo_3532_, v_hi_3533_);
    lean_dec(v_hi_3533_);
    lean_dec(v_n_3530_);
    return v_res_3534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(
    mut v___x_3535_: u8,
    mut v_x_3536_: *mut LeanObject,
    mut v_x_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_3539_: u8 = 0;
    let mut v_tail_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3537_) == 0 {
                    return v_x_3536_;
                } else {
                    v_value_3538_ = lean_ctor_get(v_x_3537_, 1);
                    v_used_3539_ = lean_ctor_get_uint8(
                        v_value_3538_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_used_3539_ == 0 {
                        v_tail_3540_ = lean_ctor_get(v_x_3537_, 2);
                        lean_inc(v_tail_3540_);
                        lean_dec_ref_known(v_x_3537_, 3);
                        v_x_3537_ = v_tail_3540_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3538_);
                        v_key_3542_ = lean_ctor_get(v_x_3537_, 0);
                        lean_inc(v_key_3542_);
                        v_tail_3543_ = lean_ctor_get(v_x_3537_, 2);
                        lean_inc(v_tail_3543_);
                        lean_dec_ref_known(v_x_3537_, 3);
                        v_stx_3544_ = lean_ctor_get(v_value_3538_, 0);
                        lean_inc(v_stx_3544_);
                        lean_dec(v_value_3538_);
                        v___x_3545_ = lean_unsigned_to_nat(1);
                        v___x_3546_ = l_Lean_Syntax_getArg(v_stx_3544_, v___x_3545_);
                        lean_dec(v_stx_3544_);
                        v___x_3552_ = l_Lean_Syntax_getRange_x3f(v___x_3546_, v___x_3535_);
                        if lean_obj_tag(v___x_3552_) == 0 {
                            v___y_3548_ = v_key_3542_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_key_3542_);
                            v_val_3553_ = lean_ctor_get(v___x_3552_, 0);
                            lean_inc(v_val_3553_);
                            lean_dec_ref_known(v___x_3552_, 1);
                            v___y_3548_ = v_val_3553_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3549_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3549_, 0, v___y_3548_);
                lean_ctor_set(v___x_3549_, 1, v___x_3546_);
                v___x_3550_ = lean_array_push(v_x_3536_, v___x_3549_);
                v_x_3536_ = v___x_3550_;
                v_x_3537_ = v_tail_3543_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6___boxed(
    mut v___x_3554_: *mut LeanObject,
    mut v_x_3555_: *mut LeanObject,
    mut v_x_3556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9396__boxed_3557_: u8 = 0;
    let mut v_res_3558_: *mut LeanObject = core::ptr::null_mut();
    v___x_9396__boxed_3557_ = (lean_unbox(v___x_3554_) as u8);
    v_res_3558_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_9396__boxed_3557_, v_x_3555_, v_x_3556_);
    return v_res_3558_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(
    mut v___x_3559_: u8,
    mut v_as_3560_: *mut LeanObject,
    mut v_i_3561_: usize,
    mut v_stop_3562_: usize,
    mut v_b_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: usize = 0;
    let mut v___x_3568_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_usize_dec_eq(v_i_3561_, v_stop_3562_);
                if v___x_3564_ == 0 {
                    v___x_3565_ = lean_array_uget_borrowed(v_as_3560_, v_i_3561_);
                    lean_inc(v___x_3565_);
                    v___x_3566_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__6(v___x_3559_, v_b_3563_, v___x_3565_);
                    v___x_3567_ = 1usize;
                    v___x_3568_ = lean_usize_add(v_i_3561_, v___x_3567_);
                    v_i_3561_ = v___x_3568_;
                    v_b_3563_ = v___x_3566_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3563_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7___boxed(
    mut v___x_3570_: *mut LeanObject,
    mut v_as_3571_: *mut LeanObject,
    mut v_i_3572_: *mut LeanObject,
    mut v_stop_3573_: *mut LeanObject,
    mut v_b_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9437__boxed_3575_: u8 = 0;
    let mut v_i_boxed_3576_: usize = 0;
    let mut v_stop_boxed_3577_: usize = 0;
    let mut v_res_3578_: *mut LeanObject = core::ptr::null_mut();
    v___x_9437__boxed_3575_ = (lean_unbox(v___x_3570_) as u8);
    v_i_boxed_3576_ = lean_unbox_usize(v_i_3572_);
    lean_dec(v_i_3572_);
    v_stop_boxed_3577_ = lean_unbox_usize(v_stop_3573_);
    lean_dec(v_stop_3573_);
    v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_9437__boxed_3575_, v_as_3571_, v_i_boxed_3576_, v_stop_boxed_3577_, v_b_3574_);
    lean_dec_ref(v_as_3571_);
    return v_res_3578_;
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(
    mut v_stx_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3590_: usize = 0;
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_unused_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3605_: u8 = 0;
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v___y_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___y_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3640_: u8 = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: u8 = 0;
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: usize = 0;
    let mut v___x_3662_: usize = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: usize = 0;
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: u8 = 0;
    let mut v_infoState_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3633_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1(v___y_3584_, v___y_3585_);
                v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
                v_isSharedCheck_3675_ = (!lean_is_exclusive(v___x_3633_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    v_isShared_3637_ = v_isSharedCheck_3675_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_3634_);
                    lean_dec(v___x_3633_);
                    v___x_3636_ = lean_box(0);
                    v_isShared_3637_ = v_isSharedCheck_3675_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                v_sz_3590_ = lean_array_size(v___y_3589_);
                v___x_3591_ = 0usize;
                lean_inc_ref(v___y_3588_);
                v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__4(v___y_3589_, v_sz_3590_, v___x_3591_, v___y_3588_, v___y_3584_, v___y_3585_);
                lean_dec_ref(v___y_3589_);
                if lean_obj_tag(v___x_3592_) == 0 {
                    v_isSharedCheck_3600_ = (!lean_is_exclusive(v___x_3592_)) as u8;
                    if v_isSharedCheck_3600_ == 0 {
                        v_unused_3601_ = lean_ctor_get(v___x_3592_, 0);
                        lean_dec(v_unused_3601_);
                        v___x_3594_ = v___x_3592_;
                        v_isShared_3595_ = v_isSharedCheck_3600_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_3592_);
                        v___x_3594_ = lean_box(0);
                        v_isShared_3595_ = v_isSharedCheck_3600_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3602_ = lean_ctor_get(v___x_3592_, 0);
                    v_isSharedCheck_3609_ = (!lean_is_exclusive(v___x_3592_)) as u8;
                    if v_isSharedCheck_3609_ == 0 {
                        v___x_3604_ = v___x_3592_;
                        v_isShared_3605_ = v_isSharedCheck_3609_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3602_);
                        lean_dec(v___x_3592_);
                        v___x_3604_ = lean_box(0);
                        v_isShared_3605_ = v_isSharedCheck_3609_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3596_ = lean_box(0);
                if v_isShared_3595_ == 0 {
                    lean_ctor_set(v___x_3594_, 0, v___x_3596_);
                    v___x_3598_ = v___x_3594_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3598_;
            }
            4 => {
                if v_isShared_3605_ == 0 {
                    v___x_3607_ = v___x_3604_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
                    v___x_3607_ = v_reuseFailAlloc_3608_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3607_;
            }
            6 => {
                v___x_3616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v___y_3613_, v___y_3614_, v___y_3611_, v___y_3615_);
                lean_dec(v___y_3615_);
                lean_dec(v___y_3613_);
                v___y_3588_ = v___y_3612_;
                v___y_3589_ = v___x_3616_;
                state = 1;
                continue;
            }
            7 => {
                v___x_3623_ = lean_nat_dec_le(v___y_3622_, v___y_3621_);
                if v___x_3623_ == 0 {
                    lean_dec(v___y_3621_);
                    lean_inc(v___y_3622_);
                    v___y_3611_ = v___y_3622_;
                    v___y_3612_ = v___y_3618_;
                    v___y_3613_ = v___y_3619_;
                    v___y_3614_ = v___y_3620_;
                    v___y_3615_ = v___y_3622_;
                    state = 6;
                    continue;
                } else {
                    v___y_3611_ = v___y_3622_;
                    v___y_3612_ = v___y_3618_;
                    v___y_3613_ = v___y_3619_;
                    v___y_3614_ = v___y_3620_;
                    v___y_3615_ = v___y_3621_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_3626_ = lean_unsigned_to_nat(0);
                v___x_3627_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__0;
                v___x_3628_ = lean_array_get_size(v___y_3625_);
                v___x_3629_ = lean_nat_dec_eq(v___x_3628_, v___x_3626_);
                if v___x_3629_ == 0 {
                    v___x_3630_ = lean_unsigned_to_nat(1);
                    v___x_3631_ = lean_nat_sub(v___x_3628_, v___x_3630_);
                    v___x_3632_ = lean_nat_dec_le(v___x_3626_, v___x_3631_);
                    if v___x_3632_ == 0 {
                        lean_inc(v___x_3631_);
                        v___y_3618_ = v___x_3627_;
                        v___y_3619_ = v___x_3628_;
                        v___y_3620_ = v___y_3625_;
                        v___y_3621_ = v___x_3631_;
                        v___y_3622_ = v___x_3631_;
                        state = 7;
                        continue;
                    } else {
                        v___y_3618_ = v___x_3627_;
                        v___y_3619_ = v___x_3628_;
                        v___y_3620_ = v___y_3625_;
                        v___y_3621_ = v___x_3631_;
                        v___y_3622_ = v___x_3626_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_3588_ = v___x_3627_;
                    v___y_3589_ = v___y_3625_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                v___x_3638_ = lean_st_ref_get(v___y_3585_);
                v___x_3671_ = l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus;
                v___x_3672_ = l_Lean_Linter_getLinterValueExtra(v___x_3671_, v_a_3634_);
                lean_dec(v_a_3634_);
                if v___x_3672_ == 0 {
                    lean_dec(v___x_3638_);
                    v___y_3640_ = v___x_3672_;
                    state = 10;
                    continue;
                } else {
                    v_infoState_3673_ = lean_ctor_get(v___x_3638_, 8);
                    lean_inc_ref(v_infoState_3673_);
                    lean_dec(v___x_3638_);
                    v_enabled_3674_ = lean_ctor_get_uint8(
                        v_infoState_3673_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref(v_infoState_3673_);
                    v___y_3640_ = v_enabled_3674_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3640_ == 0 {
                    lean_dec(v_stx_3583_);
                    v___x_3641_ = lean_box(0);
                    if v_isShared_3637_ == 0 {
                        lean_ctor_set(v___x_3636_, 0, v___x_3641_);
                        v___x_3643_ = v___x_3636_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
                        v___x_3643_ = v_reuseFailAlloc_3644_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_3645_ = lean_st_ref_get(v___y_3585_);
                    v_messages_3646_ = lean_ctor_get(v___x_3645_, 1);
                    lean_inc_ref(v_messages_3646_);
                    lean_dec(v___x_3645_);
                    v___x_3647_ = l_Lean_MessageLog_hasErrors(v_messages_3646_);
                    lean_dec_ref(v_messages_3646_);
                    if v___x_3647_ == 0 {
                        lean_del_object(v___x_3636_);
                        v___x_3648_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__3___redArg(v___y_3585_);
                        v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
                        lean_inc(v_a_3649_);
                        lean_dec_ref(v___x_3648_);
                        v___x_3650_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef;
                        v___x_3651_ = lean_st_ref_get(v___x_3650_);
                        v___f_3652_ = lean_alloc_closure(l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                        lean_closure_set(v___f_3652_, 0, v_stx_3583_);
                        lean_closure_set(v___f_3652_, 1, v___x_3651_);
                        lean_closure_set(v___f_3652_, 2, v_a_3649_);
                        v___x_3653_ = l_runST___redArg(v___f_3652_);
                        v_snd_3654_ = lean_ctor_get(v___x_3653_, 1);
                        lean_inc(v_snd_3654_);
                        lean_dec(v___x_3653_);
                        v_buckets_3655_ = lean_ctor_get(v_snd_3654_, 1);
                        lean_inc_ref(v_buckets_3655_);
                        lean_dec(v_snd_3654_);
                        v___x_3656_ = lean_unsigned_to_nat(0);
                        v___x_3657_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___closed__1;
                        v___x_3658_ = lean_array_get_size(v_buckets_3655_);
                        v___x_3659_ = lean_nat_dec_lt(v___x_3656_, v___x_3658_);
                        if v___x_3659_ == 0 {
                            lean_dec_ref(v_buckets_3655_);
                            v___y_3625_ = v___x_3657_;
                            state = 8;
                            continue;
                        } else {
                            v___x_3660_ = lean_nat_dec_le(v___x_3658_, v___x_3658_);
                            if v___x_3660_ == 0 {
                                if v___x_3659_ == 0 {
                                    lean_dec_ref(v_buckets_3655_);
                                    v___y_3625_ = v___x_3657_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_3661_ = 0usize;
                                    v___x_3662_ = lean_usize_of_nat(v___x_3658_);
                                    v___x_3663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_3647_, v_buckets_3655_, v___x_3661_, v___x_3662_, v___x_3657_);
                                    lean_dec_ref(v_buckets_3655_);
                                    v___y_3625_ = v___x_3663_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v___x_3664_ = 0usize;
                                v___x_3665_ = lean_usize_of_nat(v___x_3658_);
                                v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__7(v___x_3647_, v_buckets_3655_, v___x_3664_, v___x_3665_, v___x_3657_);
                                lean_dec_ref(v_buckets_3655_);
                                v___y_3625_ = v___x_3666_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_stx_3583_);
                        v___x_3667_ = lean_box(0);
                        if v_isShared_3637_ == 0 {
                            lean_ctor_set(v___x_3636_, 0, v___x_3667_);
                            v___x_3669_ = v___x_3636_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
                            v___x_3669_ = v_reuseFailAlloc_3670_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            11 => {
                return v___x_3643_;
            }
            12 => {
                return v___x_3669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1___boxed(
    mut v_stx_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3680_: *mut LeanObject = core::ptr::null_mut();
    v_res_3680_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter___lam__1(
        v_stx_3676_,
        v___y_3677_,
        v___y_3678_,
    );
    lean_dec(v___y_3678_);
    lean_dec_ref(v___y_3677_);
    return v_res_3680_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(
    mut v_o_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___redArg(v_o_3696_, v___y_3698_);
    return v___x_3700_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1___boxed(
    mut v_o_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3705_: *mut LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__1_spec__1(v_o_3701_, v___y_3702_, v___y_3703_);
    lean_dec(v___y_3703_);
    lean_dec_ref(v___y_3702_);
    return v_res_3705_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(
    mut v_n_3706_: *mut LeanObject,
    mut v_as_3707_: *mut LeanObject,
    mut v_lo_3708_: *mut LeanObject,
    mut v_hi_3709_: *mut LeanObject,
    mut v_w_3710_: *mut LeanObject,
    mut v_hlo_3711_: *mut LeanObject,
    mut v_hhi_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___redArg(v_n_3706_, v_as_3707_, v_lo_3708_, v_hi_3709_);
    return v___x_3713_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5___boxed(
    mut v_n_3714_: *mut LeanObject,
    mut v_as_3715_: *mut LeanObject,
    mut v_lo_3716_: *mut LeanObject,
    mut v_hi_3717_: *mut LeanObject,
    mut v_w_3718_: *mut LeanObject,
    mut v_hlo_3719_: *mut LeanObject,
    mut v_hhi_3720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3721_: *mut LeanObject = core::ptr::null_mut();
    v_res_3721_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5(v_n_3714_, v_as_3715_, v_lo_3716_, v_hi_3717_, v_w_3718_, v_hlo_3719_, v_hhi_3720_);
    lean_dec(v_hi_3717_);
    lean_dec(v_n_3714_);
    return v_res_3721_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(
    mut v_n_3722_: *mut LeanObject,
    mut v_lo_3723_: *mut LeanObject,
    mut v_hi_3724_: *mut LeanObject,
    mut v_hhi_3725_: *mut LeanObject,
    mut v_pivot_3726_: *mut LeanObject,
    mut v_as_3727_: *mut LeanObject,
    mut v_i_3728_: *mut LeanObject,
    mut v_k_3729_: *mut LeanObject,
    mut v_ilo_3730_: *mut LeanObject,
    mut v_ik_3731_: *mut LeanObject,
    mut v_w_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___redArg(v_hi_3724_, v_pivot_3726_, v_as_3727_, v_i_3728_, v_k_3729_);
    return v___x_3733_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7___boxed(
    mut v_n_3734_: *mut LeanObject,
    mut v_lo_3735_: *mut LeanObject,
    mut v_hi_3736_: *mut LeanObject,
    mut v_hhi_3737_: *mut LeanObject,
    mut v_pivot_3738_: *mut LeanObject,
    mut v_as_3739_: *mut LeanObject,
    mut v_i_3740_: *mut LeanObject,
    mut v_k_3741_: *mut LeanObject,
    mut v_ilo_3742_: *mut LeanObject,
    mut v_ik_3743_: *mut LeanObject,
    mut v_w_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3745_: *mut LeanObject = core::ptr::null_mut();
    v_res_3745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__5_spec__7(v_n_3734_, v_lo_3735_, v_hi_3736_, v_hhi_3737_, v_pivot_3738_, v_as_3739_, v_i_3740_, v_k_3741_, v_ilo_3742_, v_ik_3743_, v_w_3744_);
    lean_dec(v_hi_3736_);
    lean_dec(v_lo_3735_);
    lean_dec(v_n_3734_);
    return v_res_3745_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(
    mut v_msgData_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    v___x_3750_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___redArg(v_msgData_3746_, v___y_3748_);
    return v___x_3750_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12___boxed(
    mut v_msgData_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3755_: *mut LeanObject = core::ptr::null_mut();
    v_res_3755_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter_spec__2_spec__3_spec__5_spec__10_spec__12(v_msgData_3751_, v___y_3752_, v___y_3753_);
    lean_dec(v___y_3753_);
    lean_dec_ref(v___y_3752_);
    return v_res_3755_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_Lean_Linter_Extra_UnnecessarySeqFocus_unnecessarySeqFocusLinter;
    v___x_3758_ = l_Lean_Elab_Command_addLinter(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2____boxed(
    mut v_a_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3760_: *mut LeanObject = core::ptr::null_mut();
    v_res_3760_ = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
    return v_res_3760_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1679277753____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unnecessarySeqFocus);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3107221289____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_Extra_UnnecessarySeqFocus_multigoalKindsRef);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_UnnecessarySeqFocus_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_1921352623____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnnecessarySeqFocus_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnnecessarySeqFocus_3917858151____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
}
