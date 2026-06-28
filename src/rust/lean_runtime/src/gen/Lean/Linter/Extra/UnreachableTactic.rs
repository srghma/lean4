// Lean compiler output
// Module: Lean.Linter.Extra.UnreachableTactic
// Imports: Lean.Elab.Command Lean.Linter.Basic Lean.Parser.Syntax Init.Try
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Ord::Basic::{
    l_instOrdInt___lam__0___boxed, l_instOrdNat___lam__0___boxed, l_lexOrd___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Try::{initialize_Init_Try, runtime_initialize_Init_Try};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameHashSet_contains, l_Lean_NameHashSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
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
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_ParserExtension_instInhabitedState_default, l_Lean_Parser_parserExtension,
};
use crate::r#gen::Lean::Parser::Syntax::{
    initialize_Lean_Parser_Syntax, runtime_initialize_Lean_Parser_Syntax,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_getState___redArg;
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
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_string_dec_eq, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,8383467597245298465 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,6770064853543827592 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 116, 97, 99, 116, 105, 99, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,8412578185445384546 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,9890441027862740329 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,15277698547790567584 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [98, 105, 110, 100, 101, 114, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__4_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,6679978158056191249 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 121, 110, 97, 109, 105, 99, 81, 117, 111, 116, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,17470799606987848564 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [113, 117, 111, 116, 83, 101, 113, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__11_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,13321459889957323691 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 83, 116, 111, 112, 95, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__14_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,7782951904519764922 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__18_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,13116756686754095629 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 105, 120, 102, 105, 120, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__21_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,43679389351681793 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 84, 114, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__17_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__24_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,2224308280660100416 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__2_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__10_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__27_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject,5158953184651098857 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [113, 117, 111, 116, 0],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3_value)
        as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [116, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32, 105, 115, 32, 110, 101, 118, 101, 114, 32, 101, 120, 101, 99, 117, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1: usize = 0;
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instOrdNat___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instOrdInt___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__0_value) as *mut LeanObject,16145843736367156323 as *mut LeanObject] };
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 118, 0]};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__2_value) as *mut LeanObject,5852136541633594344 as *mut LeanObject] };
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value:
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
    m_fun: l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value:
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
        l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 84, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 84, 97, 99, 116, 105, 99, 76, 105, 110,
        116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value
) as *mut LeanObject;
static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_3:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__2_value
        ) as *mut LeanObject,
        2529909189677138316 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__3_value
        ) as *mut LeanObject,
        5485401189181365746 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value:
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
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value
) as *mut LeanObject;
pub static mut l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___closed__5_value
)
    as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(
    mut v_name_1961_: *mut LeanObject,
    mut v_decl_1962_: *mut LeanObject,
    mut v_ref_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_unused_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1965_ = lean_ctor_get(v_decl_1962_, 0);
                v_descr_1966_ = lean_ctor_get(v_decl_1962_, 1);
                v_deprecation_x3f_1967_ = lean_ctor_get(v_decl_1962_, 2);
                v___x_1968_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1969_ = (lean_unbox(v_defValue_1965_) as u8);
                lean_ctor_set_uint8(v___x_1968_, 0 as u32, v___x_1969_);
                lean_inc(v_deprecation_x3f_1967_);
                lean_inc_ref(v_descr_1966_);
                lean_inc_n(v_name_1961_, 2);
                v___x_1970_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1970_, 0, v_name_1961_);
                lean_ctor_set(v___x_1970_, 1, v_ref_1963_);
                lean_ctor_set(v___x_1970_, 2, v___x_1968_);
                lean_ctor_set(v___x_1970_, 3, v_descr_1966_);
                lean_ctor_set(v___x_1970_, 4, v_deprecation_x3f_1967_);
                v___x_1971_ = lean_register_option(v_name_1961_, v___x_1970_);
                if lean_obj_tag(v___x_1971_) == 0 {
                    v_isSharedCheck_1979_ = (!lean_is_exclusive(v___x_1971_)) as u8;
                    if v_isSharedCheck_1979_ == 0 {
                        v_unused_1980_ = lean_ctor_get(v___x_1971_, 0);
                        lean_dec(v_unused_1980_);
                        v___x_1973_ = v___x_1971_;
                        v_isShared_1974_ = v_isSharedCheck_1979_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1971_);
                        v___x_1973_ = lean_box(0);
                        v_isShared_1974_ = v_isSharedCheck_1979_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1961_);
                    v_a_1981_ = lean_ctor_get(v___x_1971_, 0);
                    v_isSharedCheck_1988_ = (!lean_is_exclusive(v___x_1971_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1983_ = v___x_1971_;
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1981_);
                        lean_dec(v___x_1971_);
                        v___x_1983_ = lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1965_);
                v___x_1975_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1975_, 0, v_name_1961_);
                lean_ctor_set(v___x_1975_, 1, v_defValue_1965_);
                if v_isShared_1974_ == 0 {
                    lean_ctor_set(v___x_1973_, 0, v___x_1975_);
                    v___x_1977_ = v___x_1973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1977_;
            }
            3 => {
                if v_isShared_1984_ == 0 {
                    v___x_1986_ = v___x_1983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1989_: *mut LeanObject,
    mut v_decl_1990_: *mut LeanObject,
    mut v_ref_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v_name_1989_, v_decl_1990_, v_ref_1991_);
    lean_dec_ref(v_decl_1990_);
    return v_res_1993_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_;
    v___x_2019_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_;
    v___x_2020_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_;
    v___x_2021_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4__spec__0(v___x_2018_, v___x_2019_, v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4____boxed(
    mut v_a_2022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2023_: *mut LeanObject = core::ptr::null_mut();
    v_res_2023_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
    return v_res_2023_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_a_2024_: *mut LeanObject,
    mut v_x_2025_: *mut LeanObject,
) -> u8 {
    let mut v___x_2026_: u8 = 0;
    let mut v_key_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2025_) == 0 {
                    v___x_2026_ = 0;
                    return v___x_2026_;
                } else {
                    v_key_2027_ = lean_ctor_get(v_x_2025_, 0);
                    v_tail_2028_ = lean_ctor_get(v_x_2025_, 2);
                    v___x_2029_ = lean_name_eq(v_key_2027_, v_a_2024_);
                    if v___x_2029_ == 0 {
                        v_x_2025_ = v_tail_2028_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2029_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_a_2031_: *mut LeanObject,
    mut v_x_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2033_: u8 = 0;
    let mut v_r_2034_: *mut LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_2031_, v_x_2032_);
    lean_dec(v_x_2032_);
    lean_dec(v_a_2031_);
    v_r_2034_ = lean_box((v_res_2033_) as usize);
    return v_r_2034_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u64 = 0;
    v___x_2035_ = lean_unsigned_to_nat(1723);
    v___x_2036_ = lean_uint64_of_nat(v___x_2035_);
    return v___x_2036_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_2037_: *mut LeanObject,
    mut v_x_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2047_: u64 = 0;
    let mut v___x_2048_: u64 = 0;
    let mut v___x_2049_: u64 = 0;
    let mut v_fold_2050_: u64 = 0;
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: u64 = 0;
    let mut v___x_2053_: u64 = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: usize = 0;
    let mut v___x_2056_: usize = 0;
    let mut v___x_2057_: usize = 0;
    let mut v___x_2058_: usize = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u64 = 0;
    let mut v_hash_2066_: u64 = 0;
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2038_) == 0 {
                    return v_x_2037_;
                } else {
                    v_key_2039_ = lean_ctor_get(v_x_2038_, 0);
                    v_value_2040_ = lean_ctor_get(v_x_2038_, 1);
                    v_tail_2041_ = lean_ctor_get(v_x_2038_, 2);
                    v_isSharedCheck_2067_ = (!lean_is_exclusive(v_x_2038_)) as u8;
                    if v_isSharedCheck_2067_ == 0 {
                        v___x_2043_ = v_x_2038_;
                        v_isShared_2044_ = v_isSharedCheck_2067_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2041_);
                        lean_inc(v_value_2040_);
                        lean_inc(v_key_2039_);
                        lean_dec(v_x_2038_);
                        v___x_2043_ = lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2067_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2045_ = lean_array_get_size(v_x_2037_);
                if lean_obj_tag(v_key_2039_) == 0 {
                    v___x_2065_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_2047_ = v___x_2065_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2066_ = lean_ctor_get_uint64(
                        v_key_2039_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2047_ = v_hash_2066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2048_ = 32u64;
                v___x_2049_ = lean_uint64_shift_right(v___y_2047_, v___x_2048_);
                v_fold_2050_ = lean_uint64_xor(v___y_2047_, v___x_2049_);
                v___x_2051_ = 16u64;
                v___x_2052_ = lean_uint64_shift_right(v_fold_2050_, v___x_2051_);
                v___x_2053_ = lean_uint64_xor(v_fold_2050_, v___x_2052_);
                v___x_2054_ = lean_uint64_to_usize(v___x_2053_);
                v___x_2055_ = lean_usize_of_nat(v___x_2045_);
                v___x_2056_ = 1usize;
                v___x_2057_ = lean_usize_sub(v___x_2055_, v___x_2056_);
                v___x_2058_ = lean_usize_land(v___x_2054_, v___x_2057_);
                v___x_2059_ = lean_array_uget_borrowed(v_x_2037_, v___x_2058_);
                lean_inc(v___x_2059_);
                if v_isShared_2044_ == 0 {
                    lean_ctor_set(v___x_2043_, 2, v___x_2059_);
                    v___x_2061_ = v___x_2043_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_key_2039_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_value_2040_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 2, v___x_2059_);
                    v___x_2061_ = v_reuseFailAlloc_2064_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2062_ = lean_array_uset(v_x_2037_, v___x_2058_, v___x_2061_);
                v_x_2037_ = v___x_2062_;
                v_x_2038_ = v_tail_2041_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(
    mut v_i_2068_: *mut LeanObject,
    mut v_source_2069_: *mut LeanObject,
    mut v_target_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v_es_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2071_ = lean_array_get_size(v_source_2069_);
                v___x_2072_ = lean_nat_dec_lt(v_i_2068_, v___x_2071_);
                if v___x_2072_ == 0 {
                    lean_dec_ref(v_source_2069_);
                    lean_dec(v_i_2068_);
                    return v_target_2070_;
                } else {
                    v_es_2073_ = lean_array_fget(v_source_2069_, v_i_2068_);
                    v___x_2074_ = lean_box(0);
                    v_source_2075_ = lean_array_fset(v_source_2069_, v_i_2068_, v___x_2074_);
                    v_target_2076_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_2070_, v_es_2073_);
                    v___x_2077_ = lean_unsigned_to_nat(1);
                    v___x_2078_ = lean_nat_add(v_i_2068_, v___x_2077_);
                    lean_dec(v_i_2068_);
                    v_i_2068_ = v___x_2078_;
                    v_source_2069_ = v_source_2075_;
                    v_target_2070_ = v_target_2076_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_data_2080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    v___x_2081_ = lean_array_get_size(v_data_2080_);
    v___x_2082_ = lean_unsigned_to_nat(2);
    v_nbuckets_2083_ = lean_nat_mul(v___x_2081_, v___x_2082_);
    v___x_2084_ = lean_unsigned_to_nat(0);
    v___x_2085_ = lean_box(0);
    v___x_2086_ = lean_mk_array(v_nbuckets_2083_, v___x_2085_);
    v___x_2087_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_2084_, v_data_2080_, v___x_2086_);
    return v___x_2087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
    mut v_b_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: u64 = 0;
    let mut v___x_2096_: u64 = 0;
    let mut v___x_2097_: u64 = 0;
    let mut v_fold_2098_: u64 = 0;
    let mut v___x_2099_: u64 = 0;
    let mut v___x_2100_: u64 = 0;
    let mut v___x_2101_: u64 = 0;
    let mut v___x_2102_: usize = 0;
    let mut v___x_2103_: usize = 0;
    let mut v___x_2104_: usize = 0;
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v_bkt_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: u8 = 0;
    let mut v_val_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut v_unused_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u64 = 0;
    let mut v_hash_2133_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2091_ = lean_ctor_get(v_m_2088_, 0);
                v_buckets_2092_ = lean_ctor_get(v_m_2088_, 1);
                v___x_2093_ = lean_array_get_size(v_buckets_2092_);
                if lean_obj_tag(v_a_2089_) == 0 {
                    v___x_2132_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_2095_ = v___x_2132_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2133_ = lean_ctor_get_uint64(
                        v_a_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2095_ = v_hash_2133_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2096_ = 32u64;
                v___x_2097_ = lean_uint64_shift_right(v___y_2095_, v___x_2096_);
                v_fold_2098_ = lean_uint64_xor(v___y_2095_, v___x_2097_);
                v___x_2099_ = 16u64;
                v___x_2100_ = lean_uint64_shift_right(v_fold_2098_, v___x_2099_);
                v___x_2101_ = lean_uint64_xor(v_fold_2098_, v___x_2100_);
                v___x_2102_ = lean_uint64_to_usize(v___x_2101_);
                v___x_2103_ = lean_usize_of_nat(v___x_2093_);
                v___x_2104_ = 1usize;
                v___x_2105_ = lean_usize_sub(v___x_2103_, v___x_2104_);
                v___x_2106_ = lean_usize_land(v___x_2102_, v___x_2105_);
                v_bkt_2107_ = lean_array_uget_borrowed(v_buckets_2092_, v___x_2106_);
                v___x_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_2089_, v_bkt_2107_);
                if v___x_2108_ == 0 {
                    lean_inc_ref(v_buckets_2092_);
                    lean_inc(v_size_2091_);
                    v_isSharedCheck_2129_ = (!lean_is_exclusive(v_m_2088_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v_unused_2130_ = lean_ctor_get(v_m_2088_, 1);
                        lean_dec(v_unused_2130_);
                        v_unused_2131_ = lean_ctor_get(v_m_2088_, 0);
                        lean_dec(v_unused_2131_);
                        v___x_2110_ = v_m_2088_;
                        v_isShared_2111_ = v_isSharedCheck_2129_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_2088_);
                        v___x_2110_ = lean_box(0);
                        v_isShared_2111_ = v_isSharedCheck_2129_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2090_);
                    lean_dec(v_a_2089_);
                    return v_m_2088_;
                }
            }
            2 => {
                v___x_2112_ = lean_unsigned_to_nat(1);
                v_size_x27_2113_ = lean_nat_add(v_size_2091_, v___x_2112_);
                lean_dec(v_size_2091_);
                lean_inc(v_bkt_2107_);
                v___x_2114_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v_a_2089_);
                lean_ctor_set(v___x_2114_, 1, v_b_2090_);
                lean_ctor_set(v___x_2114_, 2, v_bkt_2107_);
                v_buckets_x27_2115_ = lean_array_uset(v_buckets_2092_, v___x_2106_, v___x_2114_);
                v___x_2116_ = lean_unsigned_to_nat(4);
                v___x_2117_ = lean_nat_mul(v_size_x27_2113_, v___x_2116_);
                v___x_2118_ = lean_unsigned_to_nat(3);
                v___x_2119_ = lean_nat_div(v___x_2117_, v___x_2118_);
                lean_dec(v___x_2117_);
                v___x_2120_ = lean_array_get_size(v_buckets_x27_2115_);
                v___x_2121_ = lean_nat_dec_le(v___x_2119_, v___x_2120_);
                lean_dec(v___x_2119_);
                if v___x_2121_ == 0 {
                    v_val_2122_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_2115_);
                    if v_isShared_2111_ == 0 {
                        lean_ctor_set(v___x_2110_, 1, v_val_2122_);
                        lean_ctor_set(v___x_2110_, 0, v_size_x27_2113_);
                        v___x_2124_ = v___x_2110_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_size_x27_2113_);
                        lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_val_2122_);
                        v___x_2124_ = v_reuseFailAlloc_2125_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2111_ == 0 {
                        lean_ctor_set(v___x_2110_, 1, v_buckets_x27_2115_);
                        lean_ctor_set(v___x_2110_, 0, v_size_x27_2113_);
                        v___x_2127_ = v___x_2110_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_size_x27_2113_);
                        lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_buckets_x27_2115_);
                        v___x_2127_ = v_reuseFailAlloc_2128_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2124_;
            }
            4 => {
                return v___x_2127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    v___x_2134_ = lean_box(0);
    v___x_2135_ = lean_unsigned_to_nat(16);
    v___x_2136_ = lean_mk_array(v___x_2135_, v___x_2134_);
    return v___x_2136_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    v___x_2137_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__0_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2138_ = lean_unsigned_to_nat(0);
    v___x_2139_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2139_, 0, v___x_2138_);
    lean_ctor_set(v___x_2139_, 1, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__5_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2149_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__1_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2150_ = l_Lean_NameHashSet_insert(v___x_2149_, v___x_2148_);
    return v___x_2150_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    v___x_2157_ = lean_box(0);
    v___x_2158_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__8_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2159_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__6_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2159_, v___x_2158_, v___x_2157_);
    return v___x_2160_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_box(0);
    v___x_2169_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__12_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2170_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__9_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2170_, v___x_2169_, v___x_2168_);
    return v___x_2171_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2178_ = lean_box(0);
    v___x_2179_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__15_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2180_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__13_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2180_, v___x_2179_, v___x_2178_);
    return v___x_2181_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    v___x_2189_ = lean_box(0);
    v___x_2190_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__19_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2191_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__16_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2192_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2191_, v___x_2190_, v___x_2189_);
    return v___x_2192_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2199_ = lean_box(0);
    v___x_2200_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__22_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2201_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__20_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2202_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2201_, v___x_2200_, v___x_2199_);
    return v___x_2202_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2209_ = lean_box(0);
    v___x_2210_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__25_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2211_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__23_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2211_, v___x_2210_, v___x_2209_);
    return v___x_2212_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    v___x_2219_ = lean_box(0);
    v___x_2220_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__28_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_;
    v___x_2221_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__26_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v___x_2221_, v___x_2220_, v___x_2219_);
    return v___x_2222_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    v___x_2224_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn___closed__29_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_);
    v___x_2225_ = lean_st_mk_ref(v___x_2224_);
    v___x_2226_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    return v___x_2226_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2____boxed(
    mut v_a_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
    return v_res_2228_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2229_: *mut LeanObject,
    mut v_m_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_b_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0___redArg(v_m_2230_, v_a_2231_, v_b_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_x_2236_: *mut LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_2235_, v_x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_x_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2241_: u8 = 0;
    let mut v_r_2242_: *mut LeanObject = core::ptr::null_mut();
    v_res_2241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2238_, v_a_2239_, v_x_2240_);
    lean_dec(v_x_2240_);
    lean_dec(v_a_2239_);
    v_r_2242_ = lean_box((v_res_2241_) as usize);
    return v_r_2242_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2243_: *mut LeanObject,
    mut v_data_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_2244_);
    return v___x_2245_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2(
    mut v_00_u03b2_2246_: *mut LeanObject,
    mut v_i_2247_: *mut LeanObject,
    mut v_source_2248_: *mut LeanObject,
    mut v_target_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_2247_, v_source_2248_, v_target_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
    mut v_x_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_2252_, v_x_2253_);
    return v___x_2254_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(
    mut v_ignoreTacticKinds_2256_: *mut LeanObject,
    mut v_k_2257_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_k_2257_) == 1 {
        let mut v_str_2258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: u8 = 0;
        v_str_2258_ = lean_ctor_get(v_k_2257_, 1);
        v___x_2259_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___closed__0;
        v___x_2260_ = lean_string_dec_eq(v_str_2258_, v___x_2259_);
        if v___x_2260_ == 0 {
            let mut v___x_2261_: u8 = 0;
            v___x_2261_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_2256_, v_k_2257_);
            return v___x_2261_;
        } else {
            return v___x_2260_;
        }
    } else {
        let mut v___x_2262_: u8 = 0;
        v___x_2262_ = l_Lean_NameHashSet_contains(v_ignoreTacticKinds_2256_, v_k_2257_);
        return v___x_2262_;
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind___boxed(
    mut v_ignoreTacticKinds_2263_: *mut LeanObject,
    mut v_k_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2265_: u8 = 0;
    let mut v_r_2266_: *mut LeanObject = core::ptr::null_mut();
    v_res_2265_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(
        v_ignoreTacticKinds_2263_,
        v_k_2264_,
    );
    lean_dec(v_k_2264_);
    lean_dec_ref(v_ignoreTacticKinds_2263_);
    v_r_2266_ = lean_box((v_res_2265_) as usize);
    return v_r_2266_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(
    mut v_kind_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
    v___x_2270_ = lean_st_ref_take(v___x_2269_);
    v___x_2271_ = l_Lean_NameHashSet_insert(v___x_2270_, v_kind_2267_);
    v___x_2272_ = lean_st_ref_set(v___x_2269_, v___x_2271_);
    v___x_2273_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2273_, 0, v___x_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind___boxed(
    mut v_kind_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Lean_Linter_Extra_UnreachableTactic_addIgnoreTacticKind(v_kind_2274_);
    return v_res_2276_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0() -> *mut LeanObject
{
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_instMonadEIO(lean_box(0));
    return v___x_2277_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1() -> *mut LeanObject
{
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    v___x_2278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0_once),
        _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__0,
    );
    v___x_2279_ = l_StateRefT_x27_instMonad___redArg(v___x_2278_);
    return v___x_2279_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed(
    mut v_ignoreTacticKinds_2282_: *mut LeanObject,
    mut v_isTacKind_2283_: *mut LeanObject,
    mut v_x_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(
        v_ignoreTacticKinds_2282_,
        v_isTacKind_2283_,
        v_x_2284_,
        v___y_2285_,
        v___y_2286_,
    );
    lean_dec(v___y_2286_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics(
    mut v_ignoreTacticKinds_2289_: *mut LeanObject,
    mut v_isTacKind_2290_: *mut LeanObject,
    mut v_stx_2291_: *mut LeanObject,
    mut v_a_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___f_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: usize = 0;
    let mut v___x_1198__overap_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: usize = 0;
    let mut v___x_1202__overap_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2294_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1_once
                    ),
                    _init_l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__1,
                );
                if lean_obj_tag(v_stx_2291_) == 1 {
                    v_kind_2295_ = lean_ctor_get(v_stx_2291_, 1);
                    v_args_2296_ = lean_ctor_get(v_stx_2291_, 2);
                    v___x_2323_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(
                        v_ignoreTacticKinds_2289_,
                        v_kind_2295_,
                    );
                    if v___x_2323_ == 0 {
                        v___x_2324_ = lean_unsigned_to_nat(0);
                        v___x_2325_ = lean_array_get_size(v_args_2296_);
                        v___x_2326_ = lean_nat_dec_lt(v___x_2324_, v___x_2325_);
                        if v___x_2326_ == 0 {
                            lean_dec_ref(v_ignoreTacticKinds_2289_);
                            v___y_2298_ = v_a_2292_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc_ref(v_isTacKind_2290_);
                            v___f_2327_ = lean_alloc_closure(
                                l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                2,
                            );
                            lean_closure_set(v___f_2327_, 0, v_ignoreTacticKinds_2289_);
                            lean_closure_set(v___f_2327_, 1, v_isTacKind_2290_);
                            v___x_2328_ = lean_box(0);
                            v___x_2329_ = lean_nat_dec_le(v___x_2325_, v___x_2325_);
                            if v___x_2329_ == 0 {
                                if v___x_2326_ == 0 {
                                    lean_dec_ref(v___f_2327_);
                                    v___y_2298_ = v_a_2292_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2330_ = 0usize;
                                    v___x_2331_ = lean_usize_of_nat(v___x_2325_);
                                    lean_inc_ref(v_args_2296_);
                                    v___x_1198__overap_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2294_, v___f_2327_, v_args_2296_, v___x_2330_, v___x_2331_, v___x_2328_);
                                    lean_inc(v_a_2292_);
                                    v___x_2333_ = lean_apply_2(
                                        v___x_1198__overap_2332_,
                                        v_a_2292_,
                                        lean_box(0),
                                    );
                                    v___y_2322_ = v___x_2333_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___x_2334_ = 0usize;
                                v___x_2335_ = lean_usize_of_nat(v___x_2325_);
                                lean_inc_ref(v_args_2296_);
                                v___x_1202__overap_2336_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_2294_,
                                        v___f_2327_,
                                        v_args_2296_,
                                        v___x_2334_,
                                        v___x_2335_,
                                        v___x_2328_,
                                    );
                                lean_inc(v_a_2292_);
                                v___x_2337_ =
                                    lean_apply_2(v___x_1202__overap_2336_, v_a_2292_, lean_box(0));
                                v___y_2322_ = v___x_2337_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_ignoreTacticKinds_2289_);
                        v___y_2298_ = v_a_2292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_2291_);
                    lean_dec_ref(v_isTacKind_2290_);
                    lean_dec_ref(v_ignoreTacticKinds_2289_);
                    v___x_2338_ = lean_box(0);
                    v___x_2339_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2339_, 0, v___x_2338_);
                    return v___x_2339_;
                }
            }
            1 => {
                lean_inc(v_kind_2295_);
                v___x_2299_ = lean_apply_1(v_isTacKind_2290_, v_kind_2295_);
                v___x_2300_ = (lean_unbox(v___x_2299_) as u8);
                if v___x_2300_ == 0 {
                    lean_dec_ref_known(v_stx_2291_, 3);
                    v___x_2301_ = lean_box(0);
                    v___x_2302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2302_, 0, v___x_2301_);
                    return v___x_2302_;
                } else {
                    v___x_2303_ = (lean_unbox(v___x_2299_) as u8);
                    v___x_2304_ = l_Lean_Syntax_getRange_x3f(v_stx_2291_, v___x_2303_);
                    if lean_obj_tag(v___x_2304_) == 1 {
                        v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2318_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2318_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2318_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2305_);
                            lean_dec(v___x_2304_);
                            v___x_2307_ = lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2318_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2304_);
                        lean_dec_ref_known(v_stx_2291_, 3);
                        v___x_2319_ = lean_box(0);
                        v___x_2320_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2320_, 0, v___x_2319_);
                        return v___x_2320_;
                    }
                }
            }
            2 => {
                v___x_2309_ = lean_st_ref_take(v___y_2298_);
                v___x_2310_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__2;
                v___x_2311_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___closed__3;
                v___x_2312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2310_,
                    v___x_2311_,
                    v___x_2309_,
                    v_val_2305_,
                    v_stx_2291_,
                );
                v___x_2313_ = lean_st_ref_set(v___y_2298_, v___x_2312_);
                v___x_2314_ = lean_box(0);
                if v_isShared_2308_ == 0 {
                    lean_ctor_set_tag(v___x_2307_, 0);
                    lean_ctor_set(v___x_2307_, 0, v___x_2314_);
                    v___x_2316_ = v___x_2307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
                    v___x_2316_ = v_reuseFailAlloc_2317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2316_;
            }
            4 => {
                if lean_obj_tag(v___y_2322_) == 0 {
                    lean_dec_ref_known(v___y_2322_, 1);
                    v___y_2298_ = v_a_2292_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_stx_2291_, 3);
                    lean_dec_ref(v_isTacKind_2290_);
                    return v___y_2322_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics___lam__0(
    mut v_ignoreTacticKinds_2340_: *mut LeanObject,
    mut v_isTacKind_2341_: *mut LeanObject,
    mut v_x_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    v___x_2346_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(
        v_ignoreTacticKinds_2340_,
        v_isTacKind_2341_,
        v___y_2343_,
        v___y_2344_,
    );
    return v___x_2346_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics___boxed(
    mut v_ignoreTacticKinds_2347_: *mut LeanObject,
    mut v_isTacKind_2348_: *mut LeanObject,
    mut v_stx_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2352_: *mut LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics(
        v_ignoreTacticKinds_2347_,
        v_isTacKind_2348_,
        v_stx_2349_,
        v_a_2350_,
    );
    lean_dec(v_a_2350_);
    return v_res_2352_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(
    mut v_a_2353_: *mut LeanObject,
    mut v_x_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2354_) == 0 {
                    return v_x_2354_;
                } else {
                    v_key_2355_ = lean_ctor_get(v_x_2354_, 0);
                    v_value_2356_ = lean_ctor_get(v_x_2354_, 1);
                    v_tail_2357_ = lean_ctor_get(v_x_2354_, 2);
                    v_isSharedCheck_2366_ = (!lean_is_exclusive(v_x_2354_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v___x_2359_ = v_x_2354_;
                        v_isShared_2360_ = v_isSharedCheck_2366_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2357_);
                        lean_inc(v_value_2356_);
                        lean_inc(v_key_2355_);
                        lean_dec(v_x_2354_);
                        v___x_2359_ = lean_box(0);
                        v_isShared_2360_ = v_isSharedCheck_2366_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2361_ = l_Lean_Syntax_instBEqRange_beq(v_key_2355_, v_a_2353_);
                if v___x_2361_ == 0 {
                    v___x_2362_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_2353_, v_tail_2357_);
                    if v_isShared_2360_ == 0 {
                        lean_ctor_set(v___x_2359_, 2, v___x_2362_);
                        v___x_2364_ = v___x_2359_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_key_2355_);
                        lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_value_2356_);
                        lean_ctor_set(v_reuseFailAlloc_2365_, 2, v___x_2362_);
                        v___x_2364_ = v_reuseFailAlloc_2365_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2359_);
                    lean_dec(v_value_2356_);
                    lean_dec(v_key_2355_);
                    return v_tail_2357_;
                }
            }
            2 => {
                return v___x_2364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg___boxed(
    mut v_a_2367_: *mut LeanObject,
    mut v_x_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_2367_, v_x_2368_);
    lean_dec_ref(v_a_2367_);
    return v_res_2369_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(
    mut v_a_2370_: *mut LeanObject,
    mut v_x_2371_: *mut LeanObject,
) -> u8 {
    let mut v___x_2372_: u8 = 0;
    let mut v_key_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2371_) == 0 {
                    v___x_2372_ = 0;
                    return v___x_2372_;
                } else {
                    v_key_2373_ = lean_ctor_get(v_x_2371_, 0);
                    v_tail_2374_ = lean_ctor_get(v_x_2371_, 2);
                    v___x_2375_ = l_Lean_Syntax_instBEqRange_beq(v_key_2373_, v_a_2370_);
                    if v___x_2375_ == 0 {
                        v_x_2371_ = v_tail_2374_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2375_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg___boxed(
    mut v_a_2377_: *mut LeanObject,
    mut v_x_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2379_: u8 = 0;
    let mut v_r_2380_: *mut LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_2377_, v_x_2378_);
    lean_dec(v_x_2378_);
    lean_dec_ref(v_a_2377_);
    v_r_2380_ = lean_box((v_res_2379_) as usize);
    return v_r_2380_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(
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
                v___x_2399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_2382_, v_bkt_2398_);
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
                v___x_2407_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_2382_, v_bkt_2398_);
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
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg___boxed(
    mut v_m_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_2415_, v_a_2416_);
    lean_dec_ref(v_a_2416_);
    return v_res_2417_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_2418_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(
    mut v_x_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_unused_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2419_) {
                0 => {
                    v_t_2422_ = lean_ctor_get(v_x_2419_, 1);
                    lean_inc_ref(v_t_2422_);
                    lean_dec_ref_known(v_x_2419_, 2);
                    v_x_2419_ = v_t_2422_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_2424_ = lean_ctor_get(v_x_2419_, 0);
                    if lean_obj_tag(v_i_2424_) == 0 {
                        v_i_2425_ = lean_ctor_get(v_i_2424_, 0);
                        v_toElabInfo_2426_ = lean_ctor_get(v_i_2425_, 0);
                        lean_inc_ref(v_toElabInfo_2426_);
                        v_children_2427_ = lean_ctor_get(v_x_2419_, 1);
                        lean_inc_ref(v_children_2427_);
                        lean_dec_ref_known(v_x_2419_, 2);
                        v_stx_2428_ = lean_ctor_get(v_toElabInfo_2426_, 1);
                        lean_inc(v_stx_2428_);
                        lean_dec_ref(v_toElabInfo_2426_);
                        v___x_2429_ = 1;
                        v___x_2430_ = l_Lean_Syntax_getRange_x3f(v_stx_2428_, v___x_2429_);
                        lean_dec(v_stx_2428_);
                        if lean_obj_tag(v___x_2430_) == 1 {
                            v_val_2431_ = lean_ctor_get(v___x_2430_, 0);
                            lean_inc(v_val_2431_);
                            lean_dec_ref_known(v___x_2430_, 1);
                            v___x_2432_ = lean_st_ref_take(v_a_2420_);
                            v___x_2433_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v___x_2432_, v_val_2431_);
                            lean_dec(v_val_2431_);
                            v___x_2434_ = lean_st_ref_set(v_a_2420_, v___x_2433_);
                            v___x_2435_ =
                                l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(
                                    v_children_2427_,
                                    v_a_2420_,
                                );
                            return v___x_2435_;
                        } else {
                            lean_dec(v___x_2430_);
                            v___x_2436_ =
                                l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(
                                    v_children_2427_,
                                    v_a_2420_,
                                );
                            return v___x_2436_;
                        }
                    } else {
                        v_children_2437_ = lean_ctor_get(v_x_2419_, 1);
                        lean_inc_ref(v_children_2437_);
                        lean_dec_ref_known(v_x_2419_, 2);
                        v___x_2438_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(
                            v_children_2437_,
                            v_a_2420_,
                        );
                        return v___x_2438_;
                    }
                }
                _ => {
                    v_isSharedCheck_2446_ = (!lean_is_exclusive(v_x_2419_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v_unused_2447_ = lean_ctor_get(v_x_2419_, 0);
                        lean_dec(v_unused_2447_);
                        v___x_2440_ = v_x_2419_;
                        v_isShared_2441_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_2419_);
                        v___x_2440_ = lean_box(0);
                        v_isShared_2441_ = v_isSharedCheck_2446_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2442_ = lean_box(0);
                if v_isShared_2441_ == 0 {
                    lean_ctor_set_tag(v___x_2440_, 0);
                    lean_ctor_set(v___x_2440_, 0, v___x_2442_);
                    v___x_2444_ = v___x_2440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
                    v___x_2444_ = v_reuseFailAlloc_2445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(
    mut v_as_2448_: *mut LeanObject,
    mut v_i_2449_: usize,
    mut v_stop_2450_: usize,
    mut v_b_2451_: *mut LeanObject,
    mut v___y_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: usize = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2454_ = lean_usize_dec_eq(v_i_2449_, v_stop_2450_);
                if v___x_2454_ == 0 {
                    v___x_2455_ = lean_array_uget_borrowed(v_as_2448_, v_i_2449_);
                    lean_inc(v___x_2455_);
                    v___x_2456_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(
                        v___x_2455_,
                        v___y_2452_,
                    );
                    if lean_obj_tag(v___x_2456_) == 0 {
                        v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
                        lean_inc(v_a_2457_);
                        lean_dec_ref_known(v___x_2456_, 1);
                        v___x_2458_ = 1usize;
                        v___x_2459_ = lean_usize_add(v_i_2449_, v___x_2458_);
                        v_i_2449_ = v___x_2459_;
                        v_b_2451_ = v_a_2457_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2456_;
                    }
                } else {
                    v___x_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2461_, 0, v_b_2451_);
                    return v___x_2461_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(
    mut v_x_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: u8 = 0;
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: usize = 0;
    let mut v___x_2481_: usize = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut v_vs_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: u8 = 0;
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: usize = 0;
    let mut v___x_2503_: usize = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: usize = 0;
    let mut v___x_2506_: usize = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2462_) == 0 {
                    v_cs_2465_ = lean_ctor_get(v_x_2462_, 0);
                    v_isSharedCheck_2486_ = (!lean_is_exclusive(v_x_2462_)) as u8;
                    if v_isSharedCheck_2486_ == 0 {
                        v___x_2467_ = v_x_2462_;
                        v_isShared_2468_ = v_isSharedCheck_2486_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_2465_);
                        lean_dec(v_x_2462_);
                        v___x_2467_ = lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2486_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2487_ = lean_ctor_get(v_x_2462_, 0);
                    v_isSharedCheck_2508_ = (!lean_is_exclusive(v_x_2462_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2489_ = v_x_2462_;
                        v_isShared_2490_ = v_isSharedCheck_2508_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_2487_);
                        lean_dec(v_x_2462_);
                        v___x_2489_ = lean_box(0);
                        v_isShared_2490_ = v_isSharedCheck_2508_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2469_ = lean_unsigned_to_nat(0);
                v___x_2470_ = lean_array_get_size(v_cs_2465_);
                v___x_2471_ = lean_box(0);
                v___x_2472_ = lean_nat_dec_lt(v___x_2469_, v___x_2470_);
                if v___x_2472_ == 0 {
                    lean_dec_ref(v_cs_2465_);
                    if v_isShared_2468_ == 0 {
                        lean_ctor_set(v___x_2467_, 0, v___x_2471_);
                        v___x_2474_ = v___x_2467_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2471_);
                        v___x_2474_ = v_reuseFailAlloc_2475_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2476_ = lean_nat_dec_le(v___x_2470_, v___x_2470_);
                    if v___x_2476_ == 0 {
                        if v___x_2472_ == 0 {
                            lean_dec_ref(v_cs_2465_);
                            if v_isShared_2468_ == 0 {
                                lean_ctor_set(v___x_2467_, 0, v___x_2471_);
                                v___x_2478_ = v___x_2467_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2471_);
                                v___x_2478_ = v_reuseFailAlloc_2479_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2467_);
                            v___x_2480_ = 0usize;
                            v___x_2481_ = lean_usize_of_nat(v___x_2470_);
                            v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_2465_, v___x_2480_, v___x_2481_, v___x_2471_, v___y_2463_);
                            lean_dec_ref(v_cs_2465_);
                            return v___x_2482_;
                        }
                    } else {
                        lean_del_object(v___x_2467_);
                        v___x_2483_ = 0usize;
                        v___x_2484_ = lean_usize_of_nat(v___x_2470_);
                        v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_2465_, v___x_2483_, v___x_2484_, v___x_2471_, v___y_2463_);
                        lean_dec_ref(v_cs_2465_);
                        return v___x_2485_;
                    }
                }
            }
            2 => {
                return v___x_2474_;
            }
            3 => {
                return v___x_2478_;
            }
            4 => {
                v___x_2491_ = lean_unsigned_to_nat(0);
                v___x_2492_ = lean_array_get_size(v_vs_2487_);
                v___x_2493_ = lean_box(0);
                v___x_2494_ = lean_nat_dec_lt(v___x_2491_, v___x_2492_);
                if v___x_2494_ == 0 {
                    lean_dec_ref(v_vs_2487_);
                    if v_isShared_2490_ == 0 {
                        lean_ctor_set_tag(v___x_2489_, 0);
                        lean_ctor_set(v___x_2489_, 0, v___x_2493_);
                        v___x_2496_ = v___x_2489_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2493_);
                        v___x_2496_ = v_reuseFailAlloc_2497_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2498_ = lean_nat_dec_le(v___x_2492_, v___x_2492_);
                    if v___x_2498_ == 0 {
                        if v___x_2494_ == 0 {
                            lean_dec_ref(v_vs_2487_);
                            if v_isShared_2490_ == 0 {
                                lean_ctor_set_tag(v___x_2489_, 0);
                                lean_ctor_set(v___x_2489_, 0, v___x_2493_);
                                v___x_2500_ = v___x_2489_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2493_);
                                v___x_2500_ = v_reuseFailAlloc_2501_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2489_);
                            v___x_2502_ = 0usize;
                            v___x_2503_ = lean_usize_of_nat(v___x_2492_);
                            v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_2487_, v___x_2502_, v___x_2503_, v___x_2493_, v___y_2463_);
                            lean_dec_ref(v_vs_2487_);
                            return v___x_2504_;
                        }
                    } else {
                        lean_del_object(v___x_2489_);
                        v___x_2505_ = 0usize;
                        v___x_2506_ = lean_usize_of_nat(v___x_2492_);
                        v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_2487_, v___x_2505_, v___x_2506_, v___x_2493_, v___y_2463_);
                        lean_dec_ref(v_vs_2487_);
                        return v___x_2507_;
                    }
                }
            }
            5 => {
                return v___x_2496_;
            }
            6 => {
                return v___x_2500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(
    mut v_as_2509_: *mut LeanObject,
    mut v_i_2510_: usize,
    mut v_stop_2511_: usize,
    mut v_b_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: usize = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2515_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
                if v___x_2515_ == 0 {
                    v___x_2516_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
                    lean_inc(v___x_2516_);
                    v___x_2517_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v___x_2516_, v___y_2513_);
                    if lean_obj_tag(v___x_2517_) == 0 {
                        v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
                        lean_inc(v_a_2518_);
                        lean_dec_ref_known(v___x_2517_, 1);
                        v___x_2519_ = 1usize;
                        v___x_2520_ = lean_usize_add(v_i_2510_, v___x_2519_);
                        v_i_2510_ = v___x_2520_;
                        v_b_2512_ = v_a_2518_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2517_;
                    }
                } else {
                    v___x_2522_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2522_, 0, v_b_2512_);
                    return v___x_2522_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(
    mut v_x_2523_: *mut LeanObject,
    mut v_x_2524_: usize,
    mut v_x_2525_: usize,
    mut v___y_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: usize = 0;
    let mut v_j_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: usize = 0;
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut v___x_2537_: usize = 0;
    let mut v___x_2538_: usize = 0;
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: usize = 0;
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: usize = 0;
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_unused_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: usize = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: usize = 0;
    let mut v___x_2582_: usize = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2523_) == 0 {
                    v_cs_2528_ = lean_ctor_get(v_x_2523_, 0);
                    lean_inc_ref(v_cs_2528_);
                    lean_dec_ref_known(v_x_2523_, 1);
                    v___x_2529_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___closed__0);
                    v___x_2530_ = lean_usize_shift_right(v_x_2524_, v_x_2525_);
                    v_j_2531_ = lean_usize_to_nat(v___x_2530_);
                    v___x_2532_ = lean_array_get_borrowed(v___x_2529_, v_cs_2528_, v_j_2531_);
                    v___x_2533_ = 1usize;
                    v___x_2534_ = lean_usize_shift_left(v___x_2533_, v_x_2525_);
                    v___x_2535_ = lean_usize_sub(v___x_2534_, v___x_2533_);
                    v___x_2536_ = lean_usize_land(v_x_2524_, v___x_2535_);
                    v___x_2537_ = 5usize;
                    v___x_2538_ = lean_usize_sub(v_x_2525_, v___x_2537_);
                    lean_inc(v___x_2532_);
                    v___x_2539_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v___x_2532_, v___x_2536_, v___x_2538_, v___y_2526_);
                    if lean_obj_tag(v___x_2539_) == 0 {
                        v_isSharedCheck_2561_ = (!lean_is_exclusive(v___x_2539_)) as u8;
                        if v_isSharedCheck_2561_ == 0 {
                            v_unused_2562_ = lean_ctor_get(v___x_2539_, 0);
                            lean_dec(v_unused_2562_);
                            v___x_2541_ = v___x_2539_;
                            v_isShared_2542_ = v_isSharedCheck_2561_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2539_);
                            v___x_2541_ = lean_box(0);
                            v_isShared_2542_ = v_isSharedCheck_2561_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_j_2531_);
                        lean_dec_ref(v_cs_2528_);
                        return v___x_2539_;
                    }
                } else {
                    v_vs_2563_ = lean_ctor_get(v_x_2523_, 0);
                    v_isSharedCheck_2584_ = (!lean_is_exclusive(v_x_2523_)) as u8;
                    if v_isSharedCheck_2584_ == 0 {
                        v___x_2565_ = v_x_2523_;
                        v_isShared_2566_ = v_isSharedCheck_2584_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_2563_);
                        lean_dec(v_x_2523_);
                        v___x_2565_ = lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2584_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2543_ = lean_unsigned_to_nat(1);
                v___x_2544_ = lean_nat_add(v_j_2531_, v___x_2543_);
                lean_dec(v_j_2531_);
                v___x_2545_ = lean_array_get_size(v_cs_2528_);
                v___x_2546_ = lean_box(0);
                v___x_2547_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
                if v___x_2547_ == 0 {
                    lean_dec(v___x_2544_);
                    lean_dec_ref(v_cs_2528_);
                    if v_isShared_2542_ == 0 {
                        lean_ctor_set(v___x_2541_, 0, v___x_2546_);
                        v___x_2549_ = v___x_2541_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2546_);
                        v___x_2549_ = v_reuseFailAlloc_2550_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2551_ = lean_nat_dec_le(v___x_2545_, v___x_2545_);
                    if v___x_2551_ == 0 {
                        if v___x_2547_ == 0 {
                            lean_dec(v___x_2544_);
                            lean_dec_ref(v_cs_2528_);
                            if v_isShared_2542_ == 0 {
                                lean_ctor_set(v___x_2541_, 0, v___x_2546_);
                                v___x_2553_ = v___x_2541_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2546_);
                                v___x_2553_ = v_reuseFailAlloc_2554_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2541_);
                            v___x_2555_ = lean_usize_of_nat(v___x_2544_);
                            lean_dec(v___x_2544_);
                            v___x_2556_ = lean_usize_of_nat(v___x_2545_);
                            v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_2528_, v___x_2555_, v___x_2556_, v___x_2546_, v___y_2526_);
                            lean_dec_ref(v_cs_2528_);
                            return v___x_2557_;
                        }
                    } else {
                        lean_del_object(v___x_2541_);
                        v___x_2558_ = lean_usize_of_nat(v___x_2544_);
                        lean_dec(v___x_2544_);
                        v___x_2559_ = lean_usize_of_nat(v___x_2545_);
                        v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_cs_2528_, v___x_2558_, v___x_2559_, v___x_2546_, v___y_2526_);
                        lean_dec_ref(v_cs_2528_);
                        return v___x_2560_;
                    }
                }
            }
            2 => {
                return v___x_2549_;
            }
            3 => {
                return v___x_2553_;
            }
            4 => {
                v___x_2567_ = lean_usize_to_nat(v_x_2524_);
                v___x_2568_ = lean_array_get_size(v_vs_2563_);
                v___x_2569_ = lean_box(0);
                v___x_2570_ = lean_nat_dec_lt(v___x_2567_, v___x_2568_);
                if v___x_2570_ == 0 {
                    lean_dec(v___x_2567_);
                    lean_dec_ref(v_vs_2563_);
                    if v_isShared_2566_ == 0 {
                        lean_ctor_set_tag(v___x_2565_, 0);
                        lean_ctor_set(v___x_2565_, 0, v___x_2569_);
                        v___x_2572_ = v___x_2565_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2569_);
                        v___x_2572_ = v_reuseFailAlloc_2573_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2574_ = lean_nat_dec_le(v___x_2568_, v___x_2568_);
                    if v___x_2574_ == 0 {
                        if v___x_2570_ == 0 {
                            lean_dec(v___x_2567_);
                            lean_dec_ref(v_vs_2563_);
                            if v_isShared_2566_ == 0 {
                                lean_ctor_set_tag(v___x_2565_, 0);
                                lean_ctor_set(v___x_2565_, 0, v___x_2569_);
                                v___x_2576_ = v___x_2565_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2569_);
                                v___x_2576_ = v_reuseFailAlloc_2577_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2565_);
                            v___x_2578_ = lean_usize_of_nat(v___x_2567_);
                            lean_dec(v___x_2567_);
                            v___x_2579_ = lean_usize_of_nat(v___x_2568_);
                            v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_2563_, v___x_2578_, v___x_2579_, v___x_2569_, v___y_2526_);
                            lean_dec_ref(v_vs_2563_);
                            return v___x_2580_;
                        }
                    } else {
                        lean_del_object(v___x_2565_);
                        v___x_2581_ = lean_usize_of_nat(v___x_2567_);
                        lean_dec(v___x_2567_);
                        v___x_2582_ = lean_usize_of_nat(v___x_2568_);
                        v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_vs_2563_, v___x_2581_, v___x_2582_, v___x_2569_, v___y_2526_);
                        lean_dec_ref(v_vs_2563_);
                        return v___x_2583_;
                    }
                }
            }
            5 => {
                return v___x_2572_;
            }
            6 => {
                return v___x_2576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(
    mut v_t_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: usize = 0;
    let mut v___x_2606_: usize = 0;
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: usize = 0;
    let mut v___x_2609_: usize = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_unused_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2588_ = lean_ctor_get(v_t_2585_, 0);
                lean_inc_ref(v_root_2588_);
                v_tail_2589_ = lean_ctor_get(v_t_2585_, 1);
                lean_inc_ref(v_tail_2589_);
                lean_dec_ref(v_t_2585_);
                v___x_2590_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_root_2588_, v___y_2586_);
                if lean_obj_tag(v___x_2590_) == 0 {
                    v_isSharedCheck_2611_ = (!lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2611_ == 0 {
                        v_unused_2612_ = lean_ctor_get(v___x_2590_, 0);
                        lean_dec(v_unused_2612_);
                        v___x_2592_ = v___x_2590_;
                        v_isShared_2593_ = v_isSharedCheck_2611_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2590_);
                        v___x_2592_ = lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2611_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_tail_2589_);
                    return v___x_2590_;
                }
            }
            1 => {
                v___x_2594_ = lean_unsigned_to_nat(0);
                v___x_2595_ = lean_array_get_size(v_tail_2589_);
                v___x_2596_ = lean_box(0);
                v___x_2597_ = lean_nat_dec_lt(v___x_2594_, v___x_2595_);
                if v___x_2597_ == 0 {
                    lean_dec_ref(v_tail_2589_);
                    if v_isShared_2593_ == 0 {
                        lean_ctor_set(v___x_2592_, 0, v___x_2596_);
                        v___x_2599_ = v___x_2592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2596_);
                        v___x_2599_ = v_reuseFailAlloc_2600_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2601_ = lean_nat_dec_le(v___x_2595_, v___x_2595_);
                    if v___x_2601_ == 0 {
                        if v___x_2597_ == 0 {
                            lean_dec_ref(v_tail_2589_);
                            if v_isShared_2593_ == 0 {
                                lean_ctor_set(v___x_2592_, 0, v___x_2596_);
                                v___x_2603_ = v___x_2592_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2596_);
                                v___x_2603_ = v_reuseFailAlloc_2604_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2592_);
                            v___x_2605_ = 0usize;
                            v___x_2606_ = lean_usize_of_nat(v___x_2595_);
                            v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2589_, v___x_2605_, v___x_2606_, v___x_2596_, v___y_2586_);
                            lean_dec_ref(v_tail_2589_);
                            return v___x_2607_;
                        }
                    } else {
                        lean_del_object(v___x_2592_);
                        v___x_2608_ = 0usize;
                        v___x_2609_ = lean_usize_of_nat(v___x_2595_);
                        v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2589_, v___x_2608_, v___x_2609_, v___x_2596_, v___y_2586_);
                        lean_dec_ref(v_tail_2589_);
                        return v___x_2610_;
                    }
                }
            }
            2 => {
                return v___x_2599_;
            }
            3 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(
    mut v_t_2613_: *mut LeanObject,
    mut v_start_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    let mut v_root_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_2621_: usize = 0;
    let mut v_tailOff_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: usize = 0;
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: usize = 0;
    let mut v___x_2643_: usize = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_unused_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: usize = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2617_ = lean_unsigned_to_nat(0);
                v___x_2618_ = lean_nat_dec_eq(v_start_2614_, v___x_2617_);
                if v___x_2618_ == 0 {
                    v_root_2619_ = lean_ctor_get(v_t_2613_, 0);
                    lean_inc_ref(v_root_2619_);
                    v_tail_2620_ = lean_ctor_get(v_t_2613_, 1);
                    lean_inc_ref(v_tail_2620_);
                    v_shift_2621_ = lean_ctor_get_usize(v_t_2613_, 4);
                    v_tailOff_2622_ = lean_ctor_get(v_t_2613_, 3);
                    lean_inc(v_tailOff_2622_);
                    lean_dec_ref(v_t_2613_);
                    v___x_2623_ = lean_nat_dec_le(v_tailOff_2622_, v_start_2614_);
                    if v___x_2623_ == 0 {
                        lean_dec(v_tailOff_2622_);
                        v___x_2624_ = lean_usize_of_nat(v_start_2614_);
                        v___x_2625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_root_2619_, v___x_2624_, v_shift_2621_, v___y_2615_);
                        if lean_obj_tag(v___x_2625_) == 0 {
                            v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2625_)) as u8;
                            if v_isSharedCheck_2645_ == 0 {
                                v_unused_2646_ = lean_ctor_get(v___x_2625_, 0);
                                lean_dec(v_unused_2646_);
                                v___x_2627_ = v___x_2625_;
                                v_isShared_2628_ = v_isSharedCheck_2645_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_2625_);
                                v___x_2627_ = lean_box(0);
                                v_isShared_2628_ = v_isSharedCheck_2645_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_tail_2620_);
                            return v___x_2625_;
                        }
                    } else {
                        lean_dec_ref(v_root_2619_);
                        v___x_2647_ = lean_nat_sub(v_start_2614_, v_tailOff_2622_);
                        lean_dec(v_tailOff_2622_);
                        v___x_2648_ = lean_array_get_size(v_tail_2620_);
                        v___x_2649_ = lean_box(0);
                        v___x_2650_ = lean_nat_dec_lt(v___x_2647_, v___x_2648_);
                        if v___x_2650_ == 0 {
                            lean_dec(v___x_2647_);
                            lean_dec_ref(v_tail_2620_);
                            v___x_2651_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2651_, 0, v___x_2649_);
                            return v___x_2651_;
                        } else {
                            v___x_2652_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
                            if v___x_2652_ == 0 {
                                if v___x_2650_ == 0 {
                                    lean_dec(v___x_2647_);
                                    lean_dec_ref(v_tail_2620_);
                                    v___x_2653_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_2653_, 0, v___x_2649_);
                                    return v___x_2653_;
                                } else {
                                    v___x_2654_ = lean_usize_of_nat(v___x_2647_);
                                    lean_dec(v___x_2647_);
                                    v___x_2655_ = lean_usize_of_nat(v___x_2648_);
                                    v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2620_, v___x_2654_, v___x_2655_, v___x_2649_, v___y_2615_);
                                    lean_dec_ref(v_tail_2620_);
                                    return v___x_2656_;
                                }
                            } else {
                                v___x_2657_ = lean_usize_of_nat(v___x_2647_);
                                lean_dec(v___x_2647_);
                                v___x_2658_ = lean_usize_of_nat(v___x_2648_);
                                v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2620_, v___x_2657_, v___x_2658_, v___x_2649_, v___y_2615_);
                                lean_dec_ref(v_tail_2620_);
                                return v___x_2659_;
                            }
                        }
                    }
                } else {
                    v___x_2660_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_2613_, v___y_2615_);
                    return v___x_2660_;
                }
            }
            1 => {
                v___x_2629_ = lean_array_get_size(v_tail_2620_);
                v___x_2630_ = lean_box(0);
                v___x_2631_ = lean_nat_dec_lt(v___x_2617_, v___x_2629_);
                if v___x_2631_ == 0 {
                    lean_dec_ref(v_tail_2620_);
                    if v_isShared_2628_ == 0 {
                        lean_ctor_set(v___x_2627_, 0, v___x_2630_);
                        v___x_2633_ = v___x_2627_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2630_);
                        v___x_2633_ = v_reuseFailAlloc_2634_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2635_ = lean_nat_dec_le(v___x_2629_, v___x_2629_);
                    if v___x_2635_ == 0 {
                        if v___x_2631_ == 0 {
                            lean_dec_ref(v_tail_2620_);
                            if v_isShared_2628_ == 0 {
                                lean_ctor_set(v___x_2627_, 0, v___x_2630_);
                                v___x_2637_ = v___x_2627_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2630_);
                                v___x_2637_ = v_reuseFailAlloc_2638_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2627_);
                            v___x_2639_ = 0usize;
                            v___x_2640_ = lean_usize_of_nat(v___x_2629_);
                            v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2620_, v___x_2639_, v___x_2640_, v___x_2630_, v___y_2615_);
                            lean_dec_ref(v_tail_2620_);
                            return v___x_2641_;
                        }
                    } else {
                        lean_del_object(v___x_2627_);
                        v___x_2642_ = 0usize;
                        v___x_2643_ = lean_usize_of_nat(v___x_2629_);
                        v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_tail_2620_, v___x_2642_, v___x_2643_, v___x_2630_, v___y_2615_);
                        lean_dec_ref(v_tail_2620_);
                        return v___x_2644_;
                    }
                }
            }
            2 => {
                return v___x_2633_;
            }
            3 => {
                return v___x_2637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(
    mut v_trees_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2664_ = lean_unsigned_to_nat(0);
    v___x_2665_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_trees_2661_, v___x_2664_, v_a_2662_);
    return v___x_2665_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList___boxed(
    mut v_trees_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ =
        l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(v_trees_2666_, v_a_2667_);
    lean_dec(v_a_2667_);
    return v_res_2669_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1___boxed(
    mut v_as_2670_: *mut LeanObject,
    mut v_i_2671_: *mut LeanObject,
    mut v_stop_2672_: *mut LeanObject,
    mut v_b_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2676_: usize = 0;
    let mut v_stop_boxed_2677_: usize = 0;
    let mut v_res_2678_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2676_ = lean_unbox_usize(v_i_2671_);
    lean_dec(v_i_2671_);
    v_stop_boxed_2677_ = lean_unbox_usize(v_stop_2672_);
    lean_dec(v_stop_2672_);
    v_res_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__1(v_as_2670_, v_i_boxed_2676_, v_stop_boxed_2677_, v_b_2673_, v___y_2674_);
    lean_dec(v___y_2674_);
    lean_dec_ref(v_as_2670_);
    return v_res_2678_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3___boxed(
    mut v_as_2679_: *mut LeanObject,
    mut v_i_2680_: *mut LeanObject,
    mut v_stop_2681_: *mut LeanObject,
    mut v_b_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2685_: usize = 0;
    let mut v_stop_boxed_2686_: usize = 0;
    let mut v_res_2687_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2685_ = lean_unbox_usize(v_i_2680_);
    lean_dec(v_i_2680_);
    v_stop_boxed_2686_ = lean_unbox_usize(v_stop_2681_);
    lean_dec(v_stop_2681_);
    v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__3(v_as_2679_, v_i_boxed_2685_, v_stop_boxed_2686_, v_b_2682_, v___y_2683_);
    lean_dec(v___y_2683_);
    lean_dec_ref(v_as_2679_);
    return v_res_2687_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2___boxed(
    mut v_t_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2691_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__2(v_t_2688_, v___y_2689_);
    lean_dec(v___y_2689_);
    return v_res_2691_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics___boxed(
    mut v_x_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics(v_x_2692_, v_a_2693_);
    lean_dec(v_a_2693_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2___boxed(
    mut v_x_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2699_: *mut LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0_spec__2(v_x_2696_, v___y_2697_);
    lean_dec(v___y_2697_);
    return v_res_2699_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0___boxed(
    mut v_t_2700_: *mut LeanObject,
    mut v_start_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2704_: *mut LeanObject = core::ptr::null_mut();
    v_res_2704_ = l_Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0(v_t_2700_, v_start_2701_, v___y_2702_);
    lean_dec(v___y_2702_);
    lean_dec(v_start_2701_);
    return v_res_2704_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0___boxed(
    mut v_x_2705_: *mut LeanObject,
    mut v_x_2706_: *mut LeanObject,
    mut v_x_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2929__boxed_2710_: usize = 0;
    let mut v_x_2930__boxed_2711_: usize = 0;
    let mut v_res_2712_: *mut LeanObject = core::ptr::null_mut();
    v_x_2929__boxed_2710_ = lean_unbox_usize(v_x_2706_);
    lean_dec(v_x_2706_);
    v_x_2930__boxed_2711_ = lean_unbox_usize(v_x_2707_);
    lean_dec(v_x_2707_);
    v_res_2712_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList_spec__0_spec__0(v_x_2705_, v_x_2929__boxed_2710_, v_x_2930__boxed_2711_, v___y_2708_);
    lean_dec(v___y_2708_);
    return v_res_2712_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(
    mut v_00_u03b2_2713_: *mut LeanObject,
    mut v_m_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___redArg(v_m_2714_, v_a_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2___boxed(
    mut v_00_u03b2_2717_: *mut LeanObject,
    mut v_m_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2720_: *mut LeanObject = core::ptr::null_mut();
    v_res_2720_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2(v_00_u03b2_2717_, v_m_2718_, v_a_2719_);
    lean_dec_ref(v_a_2719_);
    return v_res_2720_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(
    mut v_00_u03b2_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_x_2723_: *mut LeanObject,
) -> u8 {
    let mut v___x_2724_: u8 = 0;
    v___x_2724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_2722_, v_x_2723_);
    return v___x_2724_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___boxed(
    mut v_00_u03b2_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_x_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2728_: u8 = 0;
    let mut v_r_2729_: *mut LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5(v_00_u03b2_2725_, v_a_2726_, v_x_2727_);
    lean_dec(v_x_2727_);
    lean_dec_ref(v_a_2726_);
    v_r_2729_ = lean_box((v_res_2728_) as usize);
    return v_r_2729_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(
    mut v_00_u03b2_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_x_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___redArg(v_a_2731_, v_x_2732_);
    return v___x_2733_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6___boxed(
    mut v_00_u03b2_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
    mut v_x_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2737_: *mut LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__6(v_00_u03b2_2734_, v_a_2735_, v_x_2736_);
    lean_dec_ref(v_a_2735_);
    return v_res_2737_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__0(
    mut v_a_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    v___x_2739_ = lean_nat_to_int(v_a_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(
    mut v___y_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v___x_2742_ = lean_st_ref_get(v___y_2740_);
    v_infoState_2743_ = lean_ctor_get(v___x_2742_, 8);
    lean_inc_ref(v_infoState_2743_);
    lean_dec(v___x_2742_);
    v_trees_2744_ = lean_ctor_get(v_infoState_2743_, 2);
    lean_inc_ref(v_trees_2744_);
    lean_dec_ref(v_infoState_2743_);
    v___x_2745_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2745_, 0, v_trees_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg___boxed(
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2748_: *mut LeanObject = core::ptr::null_mut();
    v_res_2748_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_2746_);
    lean_dec(v___y_2746_);
    return v_res_2748_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    v___x_2752_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_2750_);
    return v___x_2752_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___boxed(
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4(v___y_2753_, v___y_2754_);
    lean_dec(v___y_2754_);
    lean_dec_ref(v___y_2753_);
    return v_res_2756_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(
    mut v_o_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    v___x_2760_ = lean_st_ref_get(v___y_2758_);
    v_env_2761_ = lean_ctor_get(v___x_2760_, 0);
    lean_inc_ref(v_env_2761_);
    lean_dec(v___x_2760_);
    v___x_2762_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2763_ = lean_ctor_get(v___x_2762_, 0);
    v_asyncMode_2764_ = lean_ctor_get(v_toEnvExtension_2763_, 2);
    v___x_2765_ = lean_box(1);
    v___x_2766_ = lean_box(0);
    v_linterSets_2767_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2765_,
        v___x_2762_,
        v_env_2761_,
        v_asyncMode_2764_,
        v___x_2766_,
    );
    v___x_2768_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2768_, 0, v_o_2757_);
    lean_ctor_set(v___x_2768_, 1, v_linterSets_2767_);
    v___x_2769_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2769_, 0, v___x_2768_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg___boxed(
    mut v_o_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
    mut v___y_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2773_: *mut LeanObject = core::ptr::null_mut();
    v_res_2773_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_2770_, v___y_2771_);
    lean_dec(v___y_2771_);
    return v_res_2773_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v___x_2777_ = lean_st_ref_get(v___y_2775_);
    v_scopes_2778_ = lean_ctor_get(v___x_2777_, 2);
    lean_inc(v_scopes_2778_);
    lean_dec(v___x_2777_);
    v___x_2779_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2780_ = l_List_head_x21___redArg(v___x_2779_, v_scopes_2778_);
    lean_dec(v_scopes_2778_);
    v_opts_2781_ = lean_ctor_get(v___x_2780_, 1);
    lean_inc_ref(v_opts_2781_);
    lean_dec(v___x_2780_);
    v___x_2782_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_opts_2781_, v___y_2775_);
    return v___x_2782_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1___boxed(
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2786_: *mut LeanObject = core::ptr::null_mut();
    v_res_2786_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_2783_, v___y_2784_);
    lean_dec(v___y_2784_);
    lean_dec_ref(v___y_2783_);
    return v_res_2786_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2787_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__0);
    v___x_2789_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2789_, 0, v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    v___x_2790_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
    v___x_2791_ = lean_unsigned_to_nat(0);
    v___x_2792_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2792_, 0, v___x_2791_);
    lean_ctor_set(v___x_2792_, 1, v___x_2791_);
    lean_ctor_set(v___x_2792_, 2, v___x_2791_);
    lean_ctor_set(v___x_2792_, 3, v___x_2791_);
    lean_ctor_set(v___x_2792_, 4, v___x_2790_);
    lean_ctor_set(v___x_2792_, 5, v___x_2790_);
    lean_ctor_set(v___x_2792_, 6, v___x_2790_);
    lean_ctor_set(v___x_2792_, 7, v___x_2790_);
    lean_ctor_set(v___x_2792_, 8, v___x_2790_);
    lean_ctor_set(v___x_2792_, 9, v___x_2790_);
    return v___x_2792_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    v___x_2793_ = lean_unsigned_to_nat(32);
    v___x_2794_ = lean_mk_empty_array_with_capacity(v___x_2793_);
    v___x_2795_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2795_, 0, v___x_2794_);
    return v___x_2795_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2796_: usize = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    v___x_2796_ = 5usize;
    v___x_2797_ = lean_unsigned_to_nat(0);
    v___x_2798_ = lean_unsigned_to_nat(32);
    v___x_2799_ = lean_mk_empty_array_with_capacity(v___x_2798_);
    v___x_2800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__3);
    v___x_2801_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2801_, 0, v___x_2800_);
    lean_ctor_set(v___x_2801_, 1, v___x_2799_);
    lean_ctor_set(v___x_2801_, 2, v___x_2797_);
    lean_ctor_set(v___x_2801_, 3, v___x_2797_);
    lean_ctor_set_usize(v___x_2801_, 4, v___x_2796_);
    return v___x_2801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    v___x_2802_ = lean_box(1);
    v___x_2803_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__4);
    v___x_2804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__1);
    v___x_2805_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2805_, 0, v___x_2804_);
    lean_ctor_set(v___x_2805_, 1, v___x_2803_);
    lean_ctor_set(v___x_2805_, 2, v___x_2802_);
    return v___x_2805_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(
    mut v_msgData_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2809_ = lean_st_ref_get(v___y_2807_);
    v_env_2810_ = lean_ctor_get(v___x_2809_, 0);
    lean_inc_ref(v_env_2810_);
    lean_dec(v___x_2809_);
    v___x_2811_ = lean_st_ref_get(v___y_2807_);
    v_scopes_2812_ = lean_ctor_get(v___x_2811_, 2);
    lean_inc(v_scopes_2812_);
    lean_dec(v___x_2811_);
    v___x_2813_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2814_ = l_List_head_x21___redArg(v___x_2813_, v_scopes_2812_);
    lean_dec(v_scopes_2812_);
    v_opts_2815_ = lean_ctor_get(v___x_2814_, 1);
    lean_inc_ref(v_opts_2815_);
    lean_dec(v___x_2814_);
    v___x_2816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__2);
    v___x_2817_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___closed__5);
    v___x_2818_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2818_, 0, v_env_2810_);
    lean_ctor_set(v___x_2818_, 1, v___x_2816_);
    lean_ctor_set(v___x_2818_, 2, v___x_2817_);
    lean_ctor_set(v___x_2818_, 3, v_opts_2815_);
    v___x_2819_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2819_, 0, v___x_2818_);
    lean_ctor_set(v___x_2819_, 1, v_msgData_2806_);
    v___x_2820_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2820_, 0, v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg___boxed(
    mut v_msgData_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2824_: *mut LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_2821_, v___y_2822_);
    lean_dec(v___y_2822_);
    return v_res_2824_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(
    mut v_opts_2825_: *mut LeanObject,
    mut v_opt_2826_: *mut LeanObject,
) -> u8 {
    let mut v_name_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    v_name_2827_ = lean_ctor_get(v_opt_2826_, 0);
    v_defValue_2828_ = lean_ctor_get(v_opt_2826_, 1);
    v_map_2829_ = lean_ctor_get(v_opts_2825_, 0);
    v___x_2830_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2829_,
            v_name_2827_,
        );
    if lean_obj_tag(v___x_2830_) == 0 {
        let mut v___x_2831_: u8 = 0;
        v___x_2831_ = (lean_unbox(v_defValue_2828_) as u8);
        return v___x_2831_;
    } else {
        let mut v_val_2832_: *mut LeanObject = core::ptr::null_mut();
        v_val_2832_ = lean_ctor_get(v___x_2830_, 0);
        lean_inc(v_val_2832_);
        lean_dec_ref_known(v___x_2830_, 1);
        if lean_obj_tag(v_val_2832_) == 1 {
            let mut v_v_2833_: u8 = 0;
            v_v_2833_ = lean_ctor_get_uint8(v_val_2832_, 0 as u32);
            lean_dec_ref_known(v_val_2832_, 0);
            return v_v_2833_;
        } else {
            let mut v___x_2834_: u8 = 0;
            lean_dec(v_val_2832_);
            v___x_2834_ = (lean_unbox(v_defValue_2828_) as u8);
            return v___x_2834_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20___boxed(
    mut v_opts_2835_: *mut LeanObject,
    mut v_opt_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2837_: u8 = 0;
    let mut v_r_2838_: *mut LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_2835_, v_opt_2836_);
    lean_dec_ref(v_opt_2836_);
    lean_dec_ref(v_opts_2835_);
    v_r_2838_ = lean_box((v_res_2837_) as usize);
    return v_r_2838_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(
    mut v___y_2840_: u8,
    mut v_suppressElabErrors_2841_: u8,
    mut v_x_2842_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2842_) == 1 {
        let mut v_pre_2843_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2843_ = lean_ctor_get(v_x_2842_, 0);
        if lean_obj_tag(v_pre_2843_) == 0 {
            let mut v_str_2844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2846_: u8 = 0;
            v_str_2844_ = lean_ctor_get(v_x_2842_, 1);
            v___x_2845_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___closed__0;
            v___x_2846_ = lean_string_dec_eq(v_str_2844_, v___x_2845_);
            if v___x_2846_ == 0 {
                return v___y_2840_;
            } else {
                return v_suppressElabErrors_2841_;
            }
        } else {
            return v___y_2840_;
        }
    } else {
        return v___y_2840_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed(
    mut v___y_2847_: *mut LeanObject,
    mut v_suppressElabErrors_2848_: *mut LeanObject,
    mut v_x_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_12829__boxed_2850_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2851_: u8 = 0;
    let mut v_res_2852_: u8 = 0;
    let mut v_r_2853_: *mut LeanObject = core::ptr::null_mut();
    v___y_12829__boxed_2850_ = (lean_unbox(v___y_2847_) as u8);
    v_suppressElabErrors_boxed_2851_ = (lean_unbox(v_suppressElabErrors_2848_) as u8);
    v_res_2852_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0(v___y_12829__boxed_2850_, v_suppressElabErrors_boxed_2851_, v_x_2849_);
    lean_dec(v_x_2849_);
    v_r_2853_ = lean_box((v_res_2852_) as usize);
    return v_r_2853_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(
    mut v_ref_2855_: *mut LeanObject,
    mut v_msgData_2856_: *mut LeanObject,
    mut v_severity_2857_: u8,
    mut v_isSilent_2858_: u8,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2863_: u8 = 0;
    let mut v___y_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: u8 = 0;
    let mut v___y_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2877_: u8 = 0;
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut v_a_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut v___y_2926_: u8 = 0;
    let mut v___y_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2928_: u8 = 0;
    let mut v___y_2929_: u8 = 0;
    let mut v___y_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2933_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u8 = 0;
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v___y_2954_: u8 = 0;
    let mut v___y_2955_: u8 = 0;
    let mut v___y_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2957_: u8 = 0;
    let mut v___y_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: u8 = 0;
    let mut v___y_2963_: u8 = 0;
    let mut v___y_2964_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v___y_2981_: u8 = 0;
    let mut v___y_2982_: u8 = 0;
    let mut v___y_2983_: u8 = 0;
    let mut v___y_2985_: u8 = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2979_ = 2;
                v___x_2997_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2857_, v___x_2979_);
                if v___x_2997_ == 0 {
                    v___y_2985_ = v___x_2997_;
                    state = 18;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_2856_);
                    v___x_2998_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2856_);
                    v___y_2985_ = v___x_2998_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2871_ = l_Lean_Elab_Command_getScope___redArg(v___y_2870_);
                if lean_obj_tag(v___x_2871_) == 0 {
                    v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
                    lean_inc(v_a_2872_);
                    lean_dec_ref_known(v___x_2871_, 1);
                    v___x_2873_ = l_Lean_Elab_Command_getScope___redArg(v___y_2870_);
                    if lean_obj_tag(v___x_2873_) == 0 {
                        v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
                        v_isSharedCheck_2908_ = (!lean_is_exclusive(v___x_2873_)) as u8;
                        if v_isSharedCheck_2908_ == 0 {
                            v___x_2876_ = v___x_2873_;
                            v_isShared_2877_ = v_isSharedCheck_2908_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2874_);
                            lean_dec(v___x_2873_);
                            v___x_2876_ = lean_box(0);
                            v_isShared_2877_ = v_isSharedCheck_2908_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2872_);
                        lean_dec(v___y_2867_);
                        lean_dec_ref(v___y_2865_);
                        lean_dec_ref(v___y_2864_);
                        v_a_2909_ = lean_ctor_get(v___x_2873_, 0);
                        v_isSharedCheck_2916_ = (!lean_is_exclusive(v___x_2873_)) as u8;
                        if v_isSharedCheck_2916_ == 0 {
                            v___x_2911_ = v___x_2873_;
                            v_isShared_2912_ = v_isSharedCheck_2916_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2909_);
                            lean_dec(v___x_2873_);
                            v___x_2911_ = lean_box(0);
                            v_isShared_2912_ = v_isSharedCheck_2916_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2867_);
                    lean_dec_ref(v___y_2865_);
                    lean_dec_ref(v___y_2864_);
                    v_a_2917_ = lean_ctor_get(v___x_2871_, 0);
                    v_isSharedCheck_2924_ = (!lean_is_exclusive(v___x_2871_)) as u8;
                    if v_isSharedCheck_2924_ == 0 {
                        v___x_2919_ = v___x_2871_;
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2917_);
                        lean_dec(v___x_2871_);
                        v___x_2919_ = lean_box(0);
                        v_isShared_2920_ = v_isSharedCheck_2924_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2878_ = lean_st_ref_take(v___y_2870_);
                v_currNamespace_2879_ = lean_ctor_get(v_a_2872_, 2);
                lean_inc(v_currNamespace_2879_);
                lean_dec(v_a_2872_);
                v_openDecls_2880_ = lean_ctor_get(v_a_2874_, 3);
                lean_inc(v_openDecls_2880_);
                lean_dec(v_a_2874_);
                v_env_2881_ = lean_ctor_get(v___x_2878_, 0);
                v_messages_2882_ = lean_ctor_get(v___x_2878_, 1);
                v_scopes_2883_ = lean_ctor_get(v___x_2878_, 2);
                v_usedQuotCtxts_2884_ = lean_ctor_get(v___x_2878_, 3);
                v_nextMacroScope_2885_ = lean_ctor_get(v___x_2878_, 4);
                v_maxRecDepth_2886_ = lean_ctor_get(v___x_2878_, 5);
                v_ngen_2887_ = lean_ctor_get(v___x_2878_, 6);
                v_auxDeclNGen_2888_ = lean_ctor_get(v___x_2878_, 7);
                v_infoState_2889_ = lean_ctor_get(v___x_2878_, 8);
                v_traceState_2890_ = lean_ctor_get(v___x_2878_, 9);
                v_snapshotTasks_2891_ = lean_ctor_get(v___x_2878_, 10);
                v_isSharedCheck_2907_ = (!lean_is_exclusive(v___x_2878_)) as u8;
                if v_isSharedCheck_2907_ == 0 {
                    v___x_2893_ = v___x_2878_;
                    v_isShared_2894_ = v_isSharedCheck_2907_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2891_);
                    lean_inc(v_traceState_2890_);
                    lean_inc(v_infoState_2889_);
                    lean_inc(v_auxDeclNGen_2888_);
                    lean_inc(v_ngen_2887_);
                    lean_inc(v_maxRecDepth_2886_);
                    lean_inc(v_nextMacroScope_2885_);
                    lean_inc(v_usedQuotCtxts_2884_);
                    lean_inc(v_scopes_2883_);
                    lean_inc(v_messages_2882_);
                    lean_inc(v_env_2881_);
                    lean_dec(v___x_2878_);
                    v___x_2893_ = lean_box(0);
                    v_isShared_2894_ = v_isSharedCheck_2907_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2895_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2895_, 0, v_currNamespace_2879_);
                lean_ctor_set(v___x_2895_, 1, v_openDecls_2880_);
                v___x_2896_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                lean_ctor_set(v___x_2896_, 1, v___y_2864_);
                lean_inc_ref(v___y_2869_);
                lean_inc_ref(v___y_2868_);
                v___x_2897_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2897_, 0, v___y_2868_);
                lean_ctor_set(v___x_2897_, 1, v___y_2865_);
                lean_ctor_set(v___x_2897_, 2, v___y_2867_);
                lean_ctor_set(v___x_2897_, 3, v___y_2869_);
                lean_ctor_set(v___x_2897_, 4, v___x_2896_);
                lean_ctor_set_uint8(
                    v___x_2897_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2863_,
                );
                lean_ctor_set_uint8(
                    v___x_2897_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2866_,
                );
                lean_ctor_set_uint8(
                    v___x_2897_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2858_,
                );
                v___x_2898_ = l_Lean_MessageLog_add(v___x_2897_, v_messages_2882_);
                if v_isShared_2894_ == 0 {
                    lean_ctor_set(v___x_2893_, 1, v___x_2898_);
                    v___x_2900_ = v___x_2893_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_env_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2898_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_scopes_2883_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 3, v_usedQuotCtxts_2884_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 4, v_nextMacroScope_2885_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 5, v_maxRecDepth_2886_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 6, v_ngen_2887_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 7, v_auxDeclNGen_2888_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 8, v_infoState_2889_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 9, v_traceState_2890_);
                    lean_ctor_set(v_reuseFailAlloc_2906_, 10, v_snapshotTasks_2891_);
                    v___x_2900_ = v_reuseFailAlloc_2906_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2901_ = lean_st_ref_set(v___y_2870_, v___x_2900_);
                v___x_2902_ = lean_box(0);
                if v_isShared_2877_ == 0 {
                    lean_ctor_set(v___x_2876_, 0, v___x_2902_);
                    v___x_2904_ = v___x_2876_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2904_;
            }
            6 => {
                if v_isShared_2912_ == 0 {
                    v___x_2914_ = v___x_2911_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
                    v___x_2914_ = v_reuseFailAlloc_2915_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2914_;
            }
            8 => {
                if v_isShared_2920_ == 0 {
                    v___x_2922_ = v___x_2919_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2922_;
            }
            10 => {
                v_fileName_2931_ = lean_ctor_get(v___y_2859_, 0);
                v_fileMap_2932_ = lean_ctor_get(v___y_2859_, 1);
                v_suppressElabErrors_2933_ = lean_ctor_get_uint8(
                    v___y_2859_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_2934_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2856_,
                    );
                v___x_2935_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v___x_2934_, v___y_2860_);
                v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
                v_isSharedCheck_2952_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                if v_isSharedCheck_2952_ == 0 {
                    v___x_2938_ = v___x_2935_;
                    v_isShared_2939_ = v_isSharedCheck_2952_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_2936_);
                    lean_dec(v___x_2935_);
                    v___x_2938_ = lean_box(0);
                    v_isShared_2939_ = v_isSharedCheck_2952_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_2932_, 2);
                v___x_2940_ = l_Lean_FileMap_toPosition(v_fileMap_2932_, v___y_2927_);
                lean_dec(v___y_2927_);
                v___x_2941_ = l_Lean_FileMap_toPosition(v_fileMap_2932_, v___y_2930_);
                lean_dec(v___y_2930_);
                v___x_2942_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2942_, 0, v___x_2941_);
                v___x_2943_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___closed__0;
                if v_suppressElabErrors_2933_ == 0 {
                    lean_del_object(v___x_2938_);
                    v___y_2863_ = v___y_2928_;
                    v___y_2864_ = v_a_2936_;
                    v___y_2865_ = v___x_2940_;
                    v___y_2866_ = v___y_2929_;
                    v___y_2867_ = v___x_2942_;
                    v___y_2868_ = v_fileName_2931_;
                    v___y_2869_ = v___x_2943_;
                    v___y_2870_ = v___y_2860_;
                    state = 1;
                    continue;
                } else {
                    v___x_2944_ = lean_box((v___y_2926_) as usize);
                    v___x_2945_ = lean_box((v_suppressElabErrors_2933_) as usize);
                    v___f_2946_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2946_, 0, v___x_2944_);
                    lean_closure_set(v___f_2946_, 1, v___x_2945_);
                    lean_inc(v_a_2936_);
                    v___x_2947_ = l_Lean_MessageData_hasTag(v___f_2946_, v_a_2936_);
                    if v___x_2947_ == 0 {
                        lean_dec_ref_known(v___x_2942_, 1);
                        lean_dec_ref(v___x_2940_);
                        lean_dec(v_a_2936_);
                        v___x_2948_ = lean_box(0);
                        if v_isShared_2939_ == 0 {
                            lean_ctor_set(v___x_2938_, 0, v___x_2948_);
                            v___x_2950_ = v___x_2938_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
                            v___x_2950_ = v_reuseFailAlloc_2951_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2938_);
                        v___y_2863_ = v___y_2928_;
                        v___y_2864_ = v_a_2936_;
                        v___y_2865_ = v___x_2940_;
                        v___y_2866_ = v___y_2929_;
                        v___y_2867_ = v___x_2942_;
                        v___y_2868_ = v_fileName_2931_;
                        v___y_2869_ = v___x_2943_;
                        v___y_2870_ = v___y_2860_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_2950_;
            }
            13 => {
                v___x_2959_ = l_Lean_Syntax_getTailPos_x3f(v___y_2956_, v___y_2955_);
                lean_dec(v___y_2956_);
                if lean_obj_tag(v___x_2959_) == 0 {
                    lean_inc(v___y_2958_);
                    v___y_2926_ = v___y_2954_;
                    v___y_2927_ = v___y_2958_;
                    v___y_2928_ = v___y_2955_;
                    v___y_2929_ = v___y_2957_;
                    v___y_2930_ = v___y_2958_;
                    state = 10;
                    continue;
                } else {
                    v_val_2960_ = lean_ctor_get(v___x_2959_, 0);
                    lean_inc(v_val_2960_);
                    lean_dec_ref_known(v___x_2959_, 1);
                    v___y_2926_ = v___y_2954_;
                    v___y_2927_ = v___y_2958_;
                    v___y_2928_ = v___y_2955_;
                    v___y_2929_ = v___y_2957_;
                    v___y_2930_ = v_val_2960_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_2965_ = l_Lean_Elab_Command_getRef___redArg(v___y_2859_);
                if lean_obj_tag(v___x_2965_) == 0 {
                    v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
                    lean_inc(v_a_2966_);
                    lean_dec_ref_known(v___x_2965_, 1);
                    v_ref_2967_ = l_Lean_replaceRef(v_ref_2855_, v_a_2966_);
                    lean_dec(v_a_2966_);
                    v___x_2968_ = l_Lean_Syntax_getPos_x3f(v_ref_2967_, v___y_2963_);
                    if lean_obj_tag(v___x_2968_) == 0 {
                        v___x_2969_ = lean_unsigned_to_nat(0);
                        v___y_2954_ = v___y_2962_;
                        v___y_2955_ = v___y_2963_;
                        v___y_2956_ = v_ref_2967_;
                        v___y_2957_ = v___y_2964_;
                        v___y_2958_ = v___x_2969_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2970_ = lean_ctor_get(v___x_2968_, 0);
                        lean_inc(v_val_2970_);
                        lean_dec_ref_known(v___x_2968_, 1);
                        v___y_2954_ = v___y_2962_;
                        v___y_2955_ = v___y_2963_;
                        v___y_2956_ = v_ref_2967_;
                        v___y_2957_ = v___y_2964_;
                        v___y_2958_ = v_val_2970_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_2856_);
                    v_a_2971_ = lean_ctor_get(v___x_2965_, 0);
                    v_isSharedCheck_2978_ = (!lean_is_exclusive(v___x_2965_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v___x_2973_ = v___x_2965_;
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2971_);
                        lean_dec(v___x_2965_);
                        v___x_2973_ = lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2974_ == 0 {
                    v___x_2976_ = v___x_2973_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
                    v___x_2976_ = v_reuseFailAlloc_2977_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2976_;
            }
            17 => {
                if v___y_2983_ == 0 {
                    v___y_2962_ = v___y_2981_;
                    v___y_2963_ = v___y_2982_;
                    v___y_2964_ = v_severity_2857_;
                    state = 14;
                    continue;
                } else {
                    v___y_2962_ = v___y_2981_;
                    v___y_2963_ = v___y_2982_;
                    v___y_2964_ = v___x_2979_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_2985_ == 0 {
                    v___x_2986_ = lean_st_ref_get(v___y_2860_);
                    v_scopes_2987_ = lean_ctor_get(v___x_2986_, 2);
                    lean_inc(v_scopes_2987_);
                    lean_dec(v___x_2986_);
                    v___x_2988_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2989_ = l_List_head_x21___redArg(v___x_2988_, v_scopes_2987_);
                    lean_dec(v_scopes_2987_);
                    v_opts_2990_ = lean_ctor_get(v___x_2989_, 1);
                    lean_inc_ref(v_opts_2990_);
                    lean_dec(v___x_2989_);
                    v___x_2991_ = 1;
                    v___x_2992_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2857_, v___x_2991_);
                    if v___x_2992_ == 0 {
                        lean_dec_ref(v_opts_2990_);
                        v___y_2981_ = v___y_2985_;
                        v___y_2982_ = v___y_2985_;
                        v___y_2983_ = v___x_2992_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2993_ = l_Lean_warningAsError;
                        v___x_2994_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__20(v_opts_2990_, v___x_2993_);
                        lean_dec_ref(v_opts_2990_);
                        v___y_2981_ = v___y_2985_;
                        v___y_2982_ = v___y_2985_;
                        v___y_2983_ = v___x_2994_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_2856_);
                    v___x_2995_ = lean_box(0);
                    v___x_2996_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2996_, 0, v___x_2995_);
                    return v___x_2996_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13___boxed(
    mut v_ref_2999_: *mut LeanObject,
    mut v_msgData_3000_: *mut LeanObject,
    mut v_severity_3001_: *mut LeanObject,
    mut v_isSilent_3002_: *mut LeanObject,
    mut v___y_3003_: *mut LeanObject,
    mut v___y_3004_: *mut LeanObject,
    mut v___y_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3006_: u8 = 0;
    let mut v_isSilent_boxed_3007_: u8 = 0;
    let mut v_res_3008_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3006_ = (lean_unbox(v_severity_3001_) as u8);
    v_isSilent_boxed_3007_ = (lean_unbox(v_isSilent_3002_) as u8);
    v_res_3008_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_2999_, v_msgData_3000_, v_severity_boxed_3006_, v_isSilent_boxed_3007_, v___y_3003_, v___y_3004_);
    lean_dec(v___y_3004_);
    lean_dec_ref(v___y_3003_);
    lean_dec(v_ref_2999_);
    return v_res_3008_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(
    mut v_ref_3009_: *mut LeanObject,
    mut v_msgData_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    v___x_3014_ = 1;
    v___x_3015_ = 0;
    v___x_3016_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13(v_ref_3009_, v_msgData_3010_, v___x_3014_, v___x_3015_, v___y_3011_, v___y_3012_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5___boxed(
    mut v_ref_3017_: *mut LeanObject,
    mut v_msgData_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3022_: *mut LeanObject = core::ptr::null_mut();
    v_res_3022_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_ref_3017_, v_msgData_3018_, v___y_3019_, v___y_3020_);
    lean_dec(v___y_3020_);
    lean_dec_ref(v___y_3019_);
    lean_dec(v_ref_3017_);
    return v_res_3022_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__0;
    v___x_3025_ = l_Lean_stringToMessageData(v___x_3024_);
    return v___x_3025_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__2;
    v___x_3028_ = l_Lean_stringToMessageData(v___x_3027_);
    return v___x_3028_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(
    mut v_linterOption_3029_: *mut LeanObject,
    mut v_stx_3030_: *mut LeanObject,
    mut v_msg_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3052_: u8 = 0;
    let mut v_unused_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3035_ = lean_ctor_get(v_linterOption_3029_, 0);
                v_isSharedCheck_3052_ = (!lean_is_exclusive(v_linterOption_3029_)) as u8;
                if v_isSharedCheck_3052_ == 0 {
                    v_unused_3053_ = lean_ctor_get(v_linterOption_3029_, 1);
                    lean_dec(v_unused_3053_);
                    v___x_3037_ = v_linterOption_3029_;
                    v_isShared_3038_ = v_isSharedCheck_3052_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_3035_);
                    lean_dec(v_linterOption_3029_);
                    v___x_3037_ = lean_box(0);
                    v_isShared_3038_ = v_isSharedCheck_3052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3039_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__1);
                lean_inc(v_name_3035_);
                v___x_3040_ = l_Lean_MessageData_ofName(v_name_3035_);
                if v_isShared_3038_ == 0 {
                    lean_ctor_set_tag(v___x_3037_, 7);
                    lean_ctor_set(v___x_3037_, 1, v___x_3040_);
                    lean_ctor_set(v___x_3037_, 0, v___x_3039_);
                    v___x_3042_ = v___x_3037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3040_);
                    v___x_3042_ = v_reuseFailAlloc_3051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3043_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___closed__3);
                v___x_3044_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3044_, 0, v___x_3042_);
                lean_ctor_set(v___x_3044_, 1, v___x_3043_);
                v_disable_3045_ = l_Lean_MessageData_note(v___x_3044_);
                v___x_3046_ = l_Lean_Linter_linterMessageTag;
                v___x_3047_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3047_, 0, v_msg_3031_);
                lean_ctor_set(v___x_3047_, 1, v_disable_3045_);
                v___x_3048_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3048_, 0, v___x_3046_);
                lean_ctor_set(v___x_3048_, 1, v___x_3047_);
                v___x_3049_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3049_, 0, v_name_3035_);
                lean_ctor_set(v___x_3049_, 1, v___x_3048_);
                v___x_3050_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5(v_stx_3030_, v___x_3049_, v___y_3032_, v___y_3033_);
                return v___x_3050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3___boxed(
    mut v_linterOption_3054_: *mut LeanObject,
    mut v_stx_3055_: *mut LeanObject,
    mut v_msg_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3060_: *mut LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_3054_, v_stx_3055_, v_msg_3056_, v___y_3057_, v___y_3058_);
    lean_dec(v___y_3058_);
    lean_dec_ref(v___y_3057_);
    lean_dec(v_stx_3055_);
    return v_res_3060_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(
    mut v_linterOption_3061_: *mut LeanObject,
    mut v_stx_3062_: *mut LeanObject,
    mut v_msg_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3072_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3067_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_3064_, v___y_3065_);
                v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
                v_isSharedCheck_3078_ = (!lean_is_exclusive(v___x_3067_)) as u8;
                if v_isSharedCheck_3078_ == 0 {
                    v___x_3070_ = v___x_3067_;
                    v_isShared_3071_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3068_);
                    lean_dec(v___x_3067_);
                    v___x_3070_ = lean_box(0);
                    v_isShared_3071_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3072_ = l_Lean_Linter_getLinterValueExtra(v_linterOption_3061_, v_a_3068_);
                lean_dec(v_a_3068_);
                if v___x_3072_ == 0 {
                    lean_dec_ref(v_msg_3063_);
                    lean_dec_ref(v_linterOption_3061_);
                    v___x_3073_ = lean_box(0);
                    if v_isShared_3071_ == 0 {
                        lean_ctor_set(v___x_3070_, 0, v___x_3073_);
                        v___x_3075_ = v___x_3070_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
                        v___x_3075_ = v_reuseFailAlloc_3076_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3070_);
                    v___x_3077_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3(v_linterOption_3061_, v_stx_3062_, v_msg_3063_, v___y_3064_, v___y_3065_);
                    return v___x_3077_;
                }
            }
            2 => {
                return v___x_3075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2___boxed(
    mut v_linterOption_3079_: *mut LeanObject,
    mut v_stx_3080_: *mut LeanObject,
    mut v_msg_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3085_: *mut LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v_linterOption_3079_, v_stx_3080_, v_msg_3081_, v___y_3082_, v___y_3083_);
    lean_dec(v___y_3083_);
    lean_dec_ref(v___y_3082_);
    lean_dec(v_stx_3080_);
    return v_res_3085_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__1;
    v___x_3090_ = l_Lean_MessageData_ofFormat(v___x_3089_);
    return v___x_3090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(
    mut v_as_3091_: *mut LeanObject,
    mut v_sz_3092_: usize,
    mut v_i_3093_: usize,
    mut v_b_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3114_: u8 = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3103_ = lean_usize_dec_lt(v_i_3093_, v_sz_3092_);
                if v___x_3103_ == 0 {
                    v___x_3104_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3104_, 0, v_b_3094_);
                    return v___x_3104_;
                } else {
                    v_a_3105_ = lean_array_uget_borrowed(v_as_3091_, v_i_3093_);
                    v_fst_3106_ = lean_ctor_get(v_a_3105_, 0);
                    v_snd_3107_ = lean_ctor_get(v_a_3105_, 1);
                    v_start_3108_ = lean_ctor_get(v_b_3094_, 0);
                    v_stop_3109_ = lean_ctor_get(v_b_3094_, 1);
                    v_start_3110_ = lean_ctor_get(v_fst_3106_, 0);
                    v_stop_3111_ = lean_ctor_get(v_fst_3106_, 1);
                    v___x_3112_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
                    v___x_3125_ = lean_nat_dec_le(v_start_3108_, v_start_3110_);
                    if v___x_3125_ == 0 {
                        v___y_3114_ = v___x_3125_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3126_ = lean_nat_dec_le(v_stop_3111_, v_stop_3109_);
                        v___y_3114_ = v___x_3126_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3100_ = 1usize;
                v___x_3101_ = lean_usize_add(v_i_3093_, v___x_3100_);
                v_i_3093_ = v___x_3101_;
                v_b_3094_ = v_a_3099_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3114_ == 0 {
                    lean_dec_ref(v_b_3094_);
                    v___x_3115_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___closed__2);
                    v___x_3116_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2(v___x_3112_, v_snd_3107_, v___x_3115_, v___y_3095_, v___y_3096_);
                    if lean_obj_tag(v___x_3116_) == 0 {
                        lean_dec_ref_known(v___x_3116_, 1);
                        lean_inc(v_fst_3106_);
                        v_a_3099_ = v_fst_3106_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
                        v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3116_)) as u8;
                        if v_isSharedCheck_3124_ == 0 {
                            v___x_3119_ = v___x_3116_;
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3117_);
                            lean_dec(v___x_3116_);
                            v___x_3119_ = lean_box(0);
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3099_ = v_b_3094_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5___boxed(
    mut v_as_3127_: *mut LeanObject,
    mut v_sz_3128_: *mut LeanObject,
    mut v_i_3129_: *mut LeanObject,
    mut v_b_3130_: *mut LeanObject,
    mut v___y_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3134_: usize = 0;
    let mut v_i_boxed_3135_: usize = 0;
    let mut v_res_3136_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3134_ = lean_unbox_usize(v_sz_3128_);
    lean_dec(v_sz_3128_);
    v_i_boxed_3135_ = lean_unbox_usize(v_i_3129_);
    lean_dec(v_i_3129_);
    v_res_3136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v_as_3127_, v_sz_boxed_3134_, v_i_boxed_3135_, v_b_3130_, v___y_3131_, v___y_3132_);
    lean_dec(v___y_3132_);
    lean_dec_ref(v___y_3131_);
    lean_dec_ref(v_as_3127_);
    return v_res_3136_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(
    mut v_keys_3137_: *mut LeanObject,
    mut v_i_3138_: *mut LeanObject,
    mut v_k_3139_: *mut LeanObject,
) -> u8 {
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v_k_x27_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3140_ = lean_array_get_size(v_keys_3137_);
                v___x_3141_ = lean_nat_dec_lt(v_i_3138_, v___x_3140_);
                if v___x_3141_ == 0 {
                    lean_dec(v_i_3138_);
                    return v___x_3141_;
                } else {
                    v_k_x27_3142_ = lean_array_fget_borrowed(v_keys_3137_, v_i_3138_);
                    v___x_3143_ = lean_name_eq(v_k_3139_, v_k_x27_3142_);
                    if v___x_3143_ == 0 {
                        v___x_3144_ = lean_unsigned_to_nat(1);
                        v___x_3145_ = lean_nat_add(v_i_3138_, v___x_3144_);
                        lean_dec(v_i_3138_);
                        v_i_3138_ = v___x_3145_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_3138_);
                        return v___x_3143_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg___boxed(
    mut v_keys_3147_: *mut LeanObject,
    mut v_i_3148_: *mut LeanObject,
    mut v_k_3149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3150_: u8 = 0;
    let mut v_r_3151_: *mut LeanObject = core::ptr::null_mut();
    v_res_3150_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_3147_, v_i_3148_, v_k_3149_);
    lean_dec(v_k_3149_);
    lean_dec_ref(v_keys_3147_);
    v_r_3151_ = lean_box((v_res_3150_) as usize);
    return v_r_3151_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0()
-> usize {
    let mut v___x_3152_: usize = 0;
    let mut v___x_3153_: usize = 0;
    let mut v___x_3154_: usize = 0;
    v___x_3152_ = 5usize;
    v___x_3153_ = 1usize;
    v___x_3154_ = lean_usize_shift_left(v___x_3153_, v___x_3152_);
    return v___x_3154_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1()
-> usize {
    let mut v___x_3155_: usize = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    v___x_3155_ = 1usize;
    v___x_3156_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__0);
    v___x_3157_ = lean_usize_sub(v___x_3156_, v___x_3155_);
    return v___x_3157_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(
    mut v_x_3158_: *mut LeanObject,
    mut v_x_3159_: usize,
    mut v_x_3160_: *mut LeanObject,
) -> u8 {
    let mut v_es_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v_j_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v_node_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: usize = 0;
    let mut v___x_3173_: u8 = 0;
    let mut v_ks_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3158_) == 0 {
                    v_es_3161_ = lean_ctor_get(v_x_3158_, 0);
                    v___x_3162_ = lean_box(2);
                    v___x_3163_ = 5usize;
                    v___x_3164_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1);
                    v___x_3165_ = lean_usize_land(v_x_3159_, v___x_3164_);
                    v_j_3166_ = lean_usize_to_nat(v___x_3165_);
                    v___x_3167_ = lean_array_get_borrowed(v___x_3162_, v_es_3161_, v_j_3166_);
                    lean_dec(v_j_3166_);
                    match lean_obj_tag(v___x_3167_) {
                        0 => {
                            v_key_3168_ = lean_ctor_get(v___x_3167_, 0);
                            v___x_3169_ = lean_name_eq(v_x_3160_, v_key_3168_);
                            return v___x_3169_;
                        }
                        1 => {
                            v_node_3170_ = lean_ctor_get(v___x_3167_, 0);
                            v___x_3171_ = lean_usize_shift_right(v_x_3159_, v___x_3163_);
                            v_x_3158_ = v_node_3170_;
                            v_x_3159_ = v___x_3171_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3173_ = 0;
                            return v___x_3173_;
                        }
                    }
                } else {
                    v_ks_3174_ = lean_ctor_get(v_x_3158_, 0);
                    v___x_3175_ = lean_unsigned_to_nat(0);
                    v___x_3176_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_ks_3174_, v___x_3175_, v_x_3160_);
                    return v___x_3176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___boxed(
    mut v_x_3177_: *mut LeanObject,
    mut v_x_3178_: *mut LeanObject,
    mut v_x_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13305__boxed_3180_: usize = 0;
    let mut v_res_3181_: u8 = 0;
    let mut v_r_3182_: *mut LeanObject = core::ptr::null_mut();
    v_x_13305__boxed_3180_ = lean_unbox_usize(v_x_3178_);
    lean_dec(v_x_3178_);
    v_res_3181_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_3177_, v_x_13305__boxed_3180_, v_x_3179_);
    lean_dec(v_x_3179_);
    lean_dec_ref(v_x_3177_);
    v_r_3182_ = lean_box((v_res_3181_) as usize);
    return v_r_3182_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(
    mut v_x_3183_: *mut LeanObject,
    mut v_x_3184_: *mut LeanObject,
) -> u8 {
    let mut v___y_3186_: u64 = 0;
    let mut v___x_3187_: usize = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: u64 = 0;
    let mut v_hash_3190_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3184_) == 0 {
                    v___x_3189_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_3186_ = v___x_3189_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3190_ = lean_ctor_get_uint64(
                        v_x_3184_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3186_ = v_hash_3190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3187_ = lean_uint64_to_usize(v___y_3186_);
                v___x_3188_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_3183_, v___x_3187_, v_x_3184_);
                return v___x_3188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg___boxed(
    mut v_x_3191_: *mut LeanObject,
    mut v_x_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3193_: u8 = 0;
    let mut v_r_3194_: *mut LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_3191_, v_x_3192_);
    lean_dec(v_x_3192_);
    lean_dec_ref(v_x_3191_);
    v_r_3194_ = lean_box((v_res_3193_) as usize);
    return v_r_3194_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(
    mut v_x_3195_: *mut LeanObject,
    mut v_x_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u64 = 0;
    let mut v___x_3205_: u64 = 0;
    let mut v___x_3206_: u64 = 0;
    let mut v_fold_3207_: u64 = 0;
    let mut v___x_3208_: u64 = 0;
    let mut v___x_3209_: u64 = 0;
    let mut v___x_3210_: u64 = 0;
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: usize = 0;
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: usize = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3196_) == 0 {
                    return v_x_3195_;
                } else {
                    v_key_3197_ = lean_ctor_get(v_x_3196_, 0);
                    v_value_3198_ = lean_ctor_get(v_x_3196_, 1);
                    v_tail_3199_ = lean_ctor_get(v_x_3196_, 2);
                    v_isSharedCheck_3222_ = (!lean_is_exclusive(v_x_3196_)) as u8;
                    if v_isSharedCheck_3222_ == 0 {
                        v___x_3201_ = v_x_3196_;
                        v_isShared_3202_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3199_);
                        lean_inc(v_value_3198_);
                        lean_inc(v_key_3197_);
                        lean_dec(v_x_3196_);
                        v___x_3201_ = lean_box(0);
                        v_isShared_3202_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3203_ = lean_array_get_size(v_x_3195_);
                v___x_3204_ = l_Lean_Syntax_instHashableRange_hash(v_key_3197_);
                v___x_3205_ = 32u64;
                v___x_3206_ = lean_uint64_shift_right(v___x_3204_, v___x_3205_);
                v_fold_3207_ = lean_uint64_xor(v___x_3204_, v___x_3206_);
                v___x_3208_ = 16u64;
                v___x_3209_ = lean_uint64_shift_right(v_fold_3207_, v___x_3208_);
                v___x_3210_ = lean_uint64_xor(v_fold_3207_, v___x_3209_);
                v___x_3211_ = lean_uint64_to_usize(v___x_3210_);
                v___x_3212_ = lean_usize_of_nat(v___x_3203_);
                v___x_3213_ = 1usize;
                v___x_3214_ = lean_usize_sub(v___x_3212_, v___x_3213_);
                v___x_3215_ = lean_usize_land(v___x_3211_, v___x_3214_);
                v___x_3216_ = lean_array_uget_borrowed(v_x_3195_, v___x_3215_);
                lean_inc(v___x_3216_);
                if v_isShared_3202_ == 0 {
                    lean_ctor_set(v___x_3201_, 2, v___x_3216_);
                    v___x_3218_ = v___x_3201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_key_3197_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_value_3198_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 2, v___x_3216_);
                    v___x_3218_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3219_ = lean_array_uset(v_x_3195_, v___x_3215_, v___x_3218_);
                v_x_3195_ = v___x_3219_;
                v_x_3196_ = v_tail_3199_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(
    mut v_i_3223_: *mut LeanObject,
    mut v_source_3224_: *mut LeanObject,
    mut v_target_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v_es_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3226_ = lean_array_get_size(v_source_3224_);
                v___x_3227_ = lean_nat_dec_lt(v_i_3223_, v___x_3226_);
                if v___x_3227_ == 0 {
                    lean_dec_ref(v_source_3224_);
                    lean_dec(v_i_3223_);
                    return v_target_3225_;
                } else {
                    v_es_3228_ = lean_array_fget(v_source_3224_, v_i_3223_);
                    v___x_3229_ = lean_box(0);
                    v_source_3230_ = lean_array_fset(v_source_3224_, v_i_3223_, v___x_3229_);
                    v_target_3231_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_target_3225_, v_es_3228_);
                    v___x_3232_ = lean_unsigned_to_nat(1);
                    v___x_3233_ = lean_nat_add(v_i_3223_, v___x_3232_);
                    lean_dec(v_i_3223_);
                    v_i_3223_ = v___x_3233_;
                    v_source_3224_ = v_source_3230_;
                    v_target_3225_ = v_target_3231_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(
    mut v_data_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3236_ = lean_array_get_size(v_data_3235_);
    v___x_3237_ = lean_unsigned_to_nat(2);
    v_nbuckets_3238_ = lean_nat_mul(v___x_3236_, v___x_3237_);
    v___x_3239_ = lean_unsigned_to_nat(0);
    v___x_3240_ = lean_box(0);
    v___x_3241_ = lean_mk_array(v_nbuckets_3238_, v___x_3240_);
    v___x_3242_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v___x_3239_, v_data_3235_, v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(
    mut v_a_3243_: *mut LeanObject,
    mut v_b_3244_: *mut LeanObject,
    mut v_x_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3245_) == 0 {
                    lean_dec(v_b_3244_);
                    lean_dec_ref(v_a_3243_);
                    return v_x_3245_;
                } else {
                    v_key_3246_ = lean_ctor_get(v_x_3245_, 0);
                    v_value_3247_ = lean_ctor_get(v_x_3245_, 1);
                    v_tail_3248_ = lean_ctor_get(v_x_3245_, 2);
                    v_isSharedCheck_3260_ = (!lean_is_exclusive(v_x_3245_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3250_ = v_x_3245_;
                        v_isShared_3251_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3248_);
                        lean_inc(v_value_3247_);
                        lean_inc(v_key_3246_);
                        lean_dec(v_x_3245_);
                        v___x_3250_ = lean_box(0);
                        v_isShared_3251_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3252_ = l_Lean_Syntax_instBEqRange_beq(v_key_3246_, v_a_3243_);
                if v___x_3252_ == 0 {
                    v___x_3253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_3243_, v_b_3244_, v_tail_3248_);
                    if v_isShared_3251_ == 0 {
                        lean_ctor_set(v___x_3250_, 2, v___x_3253_);
                        v___x_3255_ = v___x_3250_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_key_3246_);
                        lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_value_3247_);
                        lean_ctor_set(v_reuseFailAlloc_3256_, 2, v___x_3253_);
                        v___x_3255_ = v_reuseFailAlloc_3256_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3247_);
                    lean_dec(v_key_3246_);
                    if v_isShared_3251_ == 0 {
                        lean_ctor_set(v___x_3250_, 1, v_b_3244_);
                        lean_ctor_set(v___x_3250_, 0, v_a_3243_);
                        v___x_3258_ = v___x_3250_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3243_);
                        lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_b_3244_);
                        lean_ctor_set(v_reuseFailAlloc_3259_, 2, v_tail_3248_);
                        v___x_3258_ = v_reuseFailAlloc_3259_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3255_;
            }
            3 => {
                return v___x_3258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(
    mut v_m_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_b_3263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: u64 = 0;
    let mut v___x_3271_: u64 = 0;
    let mut v___x_3272_: u64 = 0;
    let mut v_fold_3273_: u64 = 0;
    let mut v___x_3274_: u64 = 0;
    let mut v___x_3275_: u64 = 0;
    let mut v___x_3276_: u64 = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v___x_3280_: usize = 0;
    let mut v___x_3281_: usize = 0;
    let mut v_bkt_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v_val_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3264_ = lean_ctor_get(v_m_3261_, 0);
                v_buckets_3265_ = lean_ctor_get(v_m_3261_, 1);
                v_isSharedCheck_3308_ = (!lean_is_exclusive(v_m_3261_)) as u8;
                if v_isSharedCheck_3308_ == 0 {
                    v___x_3267_ = v_m_3261_;
                    v_isShared_3268_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3265_);
                    lean_inc(v_size_3264_);
                    lean_dec(v_m_3261_);
                    v___x_3267_ = lean_box(0);
                    v_isShared_3268_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3269_ = lean_array_get_size(v_buckets_3265_);
                v___x_3270_ = l_Lean_Syntax_instHashableRange_hash(v_a_3262_);
                v___x_3271_ = 32u64;
                v___x_3272_ = lean_uint64_shift_right(v___x_3270_, v___x_3271_);
                v_fold_3273_ = lean_uint64_xor(v___x_3270_, v___x_3272_);
                v___x_3274_ = 16u64;
                v___x_3275_ = lean_uint64_shift_right(v_fold_3273_, v___x_3274_);
                v___x_3276_ = lean_uint64_xor(v_fold_3273_, v___x_3275_);
                v___x_3277_ = lean_uint64_to_usize(v___x_3276_);
                v___x_3278_ = lean_usize_of_nat(v___x_3269_);
                v___x_3279_ = 1usize;
                v___x_3280_ = lean_usize_sub(v___x_3278_, v___x_3279_);
                v___x_3281_ = lean_usize_land(v___x_3277_, v___x_3280_);
                v_bkt_3282_ = lean_array_uget_borrowed(v_buckets_3265_, v___x_3281_);
                v___x_3283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Linter_Extra_UnreachableTactic_eraseUsedTactics_spec__2_spec__5___redArg(v_a_3262_, v_bkt_3282_);
                if v___x_3283_ == 0 {
                    v___x_3284_ = lean_unsigned_to_nat(1);
                    v_size_x27_3285_ = lean_nat_add(v_size_3264_, v___x_3284_);
                    lean_dec(v_size_3264_);
                    lean_inc(v_bkt_3282_);
                    v___x_3286_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3286_, 0, v_a_3262_);
                    lean_ctor_set(v___x_3286_, 1, v_b_3263_);
                    lean_ctor_set(v___x_3286_, 2, v_bkt_3282_);
                    v_buckets_x27_3287_ =
                        lean_array_uset(v_buckets_3265_, v___x_3281_, v___x_3286_);
                    v___x_3288_ = lean_unsigned_to_nat(4);
                    v___x_3289_ = lean_nat_mul(v_size_x27_3285_, v___x_3288_);
                    v___x_3290_ = lean_unsigned_to_nat(3);
                    v___x_3291_ = lean_nat_div(v___x_3289_, v___x_3290_);
                    lean_dec(v___x_3289_);
                    v___x_3292_ = lean_array_get_size(v_buckets_x27_3287_);
                    v___x_3293_ = lean_nat_dec_le(v___x_3291_, v___x_3292_);
                    lean_dec(v___x_3291_);
                    if v___x_3293_ == 0 {
                        v_val_3294_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_buckets_x27_3287_);
                        if v_isShared_3268_ == 0 {
                            lean_ctor_set(v___x_3267_, 1, v_val_3294_);
                            lean_ctor_set(v___x_3267_, 0, v_size_x27_3285_);
                            v___x_3296_ = v___x_3267_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_size_x27_3285_);
                            lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_val_3294_);
                            v___x_3296_ = v_reuseFailAlloc_3297_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3268_ == 0 {
                            lean_ctor_set(v___x_3267_, 1, v_buckets_x27_3287_);
                            lean_ctor_set(v___x_3267_, 0, v_size_x27_3285_);
                            v___x_3299_ = v___x_3267_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_size_x27_3285_);
                            lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_buckets_x27_3287_);
                            v___x_3299_ = v_reuseFailAlloc_3300_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3282_);
                    v___x_3301_ = lean_box(0);
                    v_buckets_x27_3302_ =
                        lean_array_uset(v_buckets_3265_, v___x_3281_, v___x_3301_);
                    v___x_3303_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_3262_, v_b_3263_, v_bkt_3282_);
                    v___x_3304_ = lean_array_uset(v_buckets_x27_3302_, v___x_3281_, v___x_3303_);
                    if v_isShared_3268_ == 0 {
                        lean_ctor_set(v___x_3267_, 1, v___x_3304_);
                        v___x_3306_ = v___x_3267_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_size_3264_);
                        lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3304_);
                        v___x_3306_ = v_reuseFailAlloc_3307_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3296_;
            }
            3 => {
                return v___x_3299_;
            }
            4 => {
                return v___x_3306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(
    mut v___x_3309_: *mut LeanObject,
    mut v___x_3310_: *mut LeanObject,
    mut v___y_3311_: u8,
    mut v_ignoreTacticKinds_3312_: *mut LeanObject,
    mut v_stx_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3318_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: u8 = 0;
    let mut v___y_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: usize = 0;
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: usize = 0;
    let mut v___x_3354_: usize = 0;
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_stx_3313_) == 1 {
                    v_kind_3336_ = lean_ctor_get(v_stx_3313_, 1);
                    v_args_3337_ = lean_ctor_get(v_stx_3313_, 2);
                    v___x_3344_ = l_Lean_Linter_Extra_UnreachableTactic_isIgnoreTacticKind(
                        v_ignoreTacticKinds_3312_,
                        v_kind_3336_,
                    );
                    if v___x_3344_ == 0 {
                        v___x_3345_ = lean_unsigned_to_nat(0);
                        v___x_3346_ = lean_array_get_size(v_args_3337_);
                        v___x_3347_ = lean_nat_dec_lt(v___x_3345_, v___x_3346_);
                        if v___x_3347_ == 0 {
                            v___y_3339_ = v_a_3314_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3348_ = lean_box(0);
                            v___x_3349_ = lean_nat_dec_le(v___x_3346_, v___x_3346_);
                            if v___x_3349_ == 0 {
                                if v___x_3347_ == 0 {
                                    v___y_3339_ = v_a_3314_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_3350_ = 0usize;
                                    v___x_3351_ = lean_usize_of_nat(v___x_3346_);
                                    v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_3309_, v___x_3310_, v___y_3311_, v_ignoreTacticKinds_3312_, v_args_3337_, v___x_3350_, v___x_3351_, v___x_3348_, v_a_3314_);
                                    v___y_3343_ = v___x_3352_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___x_3353_ = 0usize;
                                v___x_3354_ = lean_usize_of_nat(v___x_3346_);
                                v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_3309_, v___x_3310_, v___y_3311_, v_ignoreTacticKinds_3312_, v_args_3337_, v___x_3353_, v___x_3354_, v___x_3348_, v_a_3314_);
                                v___y_3343_ = v___x_3355_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___y_3339_ = v_a_3314_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_3313_);
                    v___x_3356_ = lean_box(0);
                    v___x_3357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3357_, 0, v___x_3356_);
                    return v___x_3357_;
                }
            }
            1 => {
                if v___y_3318_ == 0 {
                    lean_dec(v_stx_3313_);
                    v___x_3319_ = lean_box(0);
                    v___x_3320_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3320_, 0, v___x_3319_);
                    return v___x_3320_;
                } else {
                    v___x_3321_ = l_Lean_Syntax_getRange_x3f(v_stx_3313_, v___y_3318_);
                    if lean_obj_tag(v___x_3321_) == 1 {
                        v_val_3322_ = lean_ctor_get(v___x_3321_, 0);
                        v_isSharedCheck_3333_ = (!lean_is_exclusive(v___x_3321_)) as u8;
                        if v_isSharedCheck_3333_ == 0 {
                            v___x_3324_ = v___x_3321_;
                            v_isShared_3325_ = v_isSharedCheck_3333_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_3322_);
                            lean_dec(v___x_3321_);
                            v___x_3324_ = lean_box(0);
                            v_isShared_3325_ = v_isSharedCheck_3333_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3321_);
                        lean_dec(v_stx_3313_);
                        v___x_3334_ = lean_box(0);
                        v___x_3335_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3335_, 0, v___x_3334_);
                        return v___x_3335_;
                    }
                }
            }
            2 => {
                v___x_3326_ = lean_st_ref_take(v___y_3317_);
                v___x_3327_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v___x_3326_, v_val_3322_, v_stx_3313_);
                v___x_3328_ = lean_st_ref_set(v___y_3317_, v___x_3327_);
                v___x_3329_ = lean_box(0);
                if v_isShared_3325_ == 0 {
                    lean_ctor_set_tag(v___x_3324_, 0);
                    lean_ctor_set(v___x_3324_, 0, v___x_3329_);
                    v___x_3331_ = v___x_3324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3331_;
            }
            4 => {
                v___x_3340_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_3309_, v_kind_3336_);
                if v___x_3340_ == 0 {
                    v___x_3341_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v___x_3310_, v_kind_3336_);
                    v___y_3317_ = v___y_3339_;
                    v___y_3318_ = v___x_3341_;
                    state = 1;
                    continue;
                } else {
                    v___y_3317_ = v___y_3339_;
                    v___y_3318_ = v___y_3311_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v___y_3343_) == 0 {
                    lean_dec_ref_known(v___y_3343_, 1);
                    v___y_3339_ = v_a_3314_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref_known(v_stx_3313_, 3);
                    return v___y_3343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(
    mut v___x_3358_: *mut LeanObject,
    mut v___x_3359_: *mut LeanObject,
    mut v___y_3360_: u8,
    mut v_ignoreTacticKinds_3361_: *mut LeanObject,
    mut v_as_3362_: *mut LeanObject,
    mut v_i_3363_: usize,
    mut v_stop_3364_: usize,
    mut v_b_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: usize = 0;
    let mut v___x_3373_: usize = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3368_ = lean_usize_dec_eq(v_i_3363_, v_stop_3364_);
                if v___x_3368_ == 0 {
                    v___x_3369_ = lean_array_uget_borrowed(v_as_3362_, v_i_3363_);
                    lean_inc(v___x_3369_);
                    v___x_3370_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_3358_, v___x_3359_, v___y_3360_, v_ignoreTacticKinds_3361_, v___x_3369_, v___y_3366_);
                    if lean_obj_tag(v___x_3370_) == 0 {
                        v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
                        lean_inc(v_a_3371_);
                        lean_dec_ref_known(v___x_3370_, 1);
                        v___x_3372_ = 1usize;
                        v___x_3373_ = lean_usize_add(v_i_3363_, v___x_3372_);
                        v_i_3363_ = v___x_3373_;
                        v_b_3365_ = v_a_3371_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3370_;
                    }
                } else {
                    v___x_3375_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3375_, 0, v_b_3365_);
                    return v___x_3375_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16___boxed(
    mut v___x_3376_: *mut LeanObject,
    mut v___x_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v_ignoreTacticKinds_3379_: *mut LeanObject,
    mut v_as_3380_: *mut LeanObject,
    mut v_i_3381_: *mut LeanObject,
    mut v_stop_3382_: *mut LeanObject,
    mut v_b_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_13562__boxed_3386_: u8 = 0;
    let mut v_i_boxed_3387_: usize = 0;
    let mut v_stop_boxed_3388_: usize = 0;
    let mut v_res_3389_: *mut LeanObject = core::ptr::null_mut();
    v___y_13562__boxed_3386_ = (lean_unbox(v___y_3378_) as u8);
    v_i_boxed_3387_ = lean_unbox_usize(v_i_3381_);
    lean_dec(v_i_3381_);
    v_stop_boxed_3388_ = lean_unbox_usize(v_stop_3382_);
    lean_dec(v_stop_3382_);
    v_res_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__16(v___x_3376_, v___x_3377_, v___y_13562__boxed_3386_, v_ignoreTacticKinds_3379_, v_as_3380_, v_i_boxed_3387_, v_stop_boxed_3388_, v_b_3383_, v___y_3384_);
    lean_dec(v___y_3384_);
    lean_dec_ref(v_as_3380_);
    lean_dec_ref(v_ignoreTacticKinds_3379_);
    lean_dec_ref(v___x_3377_);
    lean_dec_ref(v___x_3376_);
    return v_res_3389_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10___boxed(
    mut v___x_3390_: *mut LeanObject,
    mut v___x_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v_ignoreTacticKinds_3393_: *mut LeanObject,
    mut v_stx_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_13576__boxed_3397_: u8 = 0;
    let mut v_res_3398_: *mut LeanObject = core::ptr::null_mut();
    v___y_13576__boxed_3397_ = (lean_unbox(v___y_3392_) as u8);
    v_res_3398_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v___x_3390_, v___x_3391_, v___y_13576__boxed_3397_, v_ignoreTacticKinds_3393_, v_stx_3394_, v_a_3395_);
    lean_dec(v_a_3395_);
    lean_dec_ref(v_ignoreTacticKinds_3393_);
    lean_dec_ref(v___x_3391_);
    lean_dec_ref(v___x_3390_);
    return v_res_3398_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(
    mut v_keys_3399_: *mut LeanObject,
    mut v_vals_3400_: *mut LeanObject,
    mut v_i_3401_: *mut LeanObject,
    mut v_k_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3403_ = lean_array_get_size(v_keys_3399_);
                v___x_3404_ = lean_nat_dec_lt(v_i_3401_, v___x_3403_);
                if v___x_3404_ == 0 {
                    lean_dec(v_i_3401_);
                    v___x_3405_ = lean_box(0);
                    return v___x_3405_;
                } else {
                    v_k_x27_3406_ = lean_array_fget_borrowed(v_keys_3399_, v_i_3401_);
                    v___x_3407_ = lean_name_eq(v_k_3402_, v_k_x27_3406_);
                    if v___x_3407_ == 0 {
                        v___x_3408_ = lean_unsigned_to_nat(1);
                        v___x_3409_ = lean_nat_add(v_i_3401_, v___x_3408_);
                        lean_dec(v_i_3401_);
                        v_i_3401_ = v___x_3409_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3411_ = lean_array_fget_borrowed(v_vals_3400_, v_i_3401_);
                        lean_dec(v_i_3401_);
                        lean_inc(v___x_3411_);
                        v___x_3412_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3412_, 0, v___x_3411_);
                        return v___x_3412_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_keys_3413_: *mut LeanObject,
    mut v_vals_3414_: *mut LeanObject,
    mut v_i_3415_: *mut LeanObject,
    mut v_k_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3417_: *mut LeanObject = core::ptr::null_mut();
    v_res_3417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_3413_, v_vals_3414_, v_i_3415_, v_k_3416_);
    lean_dec(v_k_3416_);
    lean_dec_ref(v_vals_3414_);
    lean_dec_ref(v_keys_3413_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(
    mut v_x_3418_: *mut LeanObject,
    mut v_x_3419_: usize,
    mut v_x_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: usize = 0;
    let mut v___x_3424_: usize = 0;
    let mut v___x_3425_: usize = 0;
    let mut v_j_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: usize = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3418_) == 0 {
                    v_es_3421_ = lean_ctor_get(v_x_3418_, 0);
                    v___x_3422_ = lean_box(2);
                    v___x_3423_ = 5usize;
                    v___x_3424_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg___closed__1);
                    v___x_3425_ = lean_usize_land(v_x_3419_, v___x_3424_);
                    v_j_3426_ = lean_usize_to_nat(v___x_3425_);
                    v___x_3427_ = lean_array_get_borrowed(v___x_3422_, v_es_3421_, v_j_3426_);
                    lean_dec(v_j_3426_);
                    match lean_obj_tag(v___x_3427_) {
                        0 => {
                            v_key_3428_ = lean_ctor_get(v___x_3427_, 0);
                            v_val_3429_ = lean_ctor_get(v___x_3427_, 1);
                            v___x_3430_ = lean_name_eq(v_x_3420_, v_key_3428_);
                            if v___x_3430_ == 0 {
                                v___x_3431_ = lean_box(0);
                                return v___x_3431_;
                            } else {
                                lean_inc(v_val_3429_);
                                v___x_3432_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3432_, 0, v_val_3429_);
                                return v___x_3432_;
                            }
                        }
                        1 => {
                            v_node_3433_ = lean_ctor_get(v___x_3427_, 0);
                            v___x_3434_ = lean_usize_shift_right(v_x_3419_, v___x_3423_);
                            v_x_3418_ = v_node_3433_;
                            v_x_3419_ = v___x_3434_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3436_ = lean_box(0);
                            return v___x_3436_;
                        }
                    }
                } else {
                    v_ks_3437_ = lean_ctor_get(v_x_3418_, 0);
                    v_vs_3438_ = lean_ctor_get(v_x_3418_, 1);
                    v___x_3439_ = lean_unsigned_to_nat(0);
                    v___x_3440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_ks_3437_, v_vs_3438_, v___x_3439_, v_x_3420_);
                    return v___x_3440_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg___boxed(
    mut v_x_3441_: *mut LeanObject,
    mut v_x_3442_: *mut LeanObject,
    mut v_x_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13716__boxed_3444_: usize = 0;
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_x_13716__boxed_3444_ = lean_unbox_usize(v_x_3442_);
    lean_dec(v_x_3442_);
    v_res_3445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_3441_, v_x_13716__boxed_3444_, v_x_3443_);
    lean_dec(v_x_3443_);
    lean_dec_ref(v_x_3441_);
    return v_res_3445_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(
    mut v_x_3446_: *mut LeanObject,
    mut v_x_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3449_: u64 = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u64 = 0;
    let mut v_hash_3453_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3447_) == 0 {
                    v___x_3452_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_3449_ = v___x_3452_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3453_ = lean_ctor_get_uint64(
                        v_x_3447_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3449_ = v_hash_3453_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3450_ = lean_uint64_to_usize(v___y_3449_);
                v___x_3451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_3446_, v___x_3450_, v_x_3447_);
                return v___x_3451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg___boxed(
    mut v_x_3454_: *mut LeanObject,
    mut v_x_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_3454_, v_x_3455_);
    lean_dec(v_x_3455_);
    lean_dec_ref(v_x_3454_);
    return v_res_3456_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(
    mut v_x_3457_: *mut LeanObject,
    mut v_x_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3458_) == 0 {
                    return v_x_3457_;
                } else {
                    v_key_3459_ = lean_ctor_get(v_x_3458_, 0);
                    v_value_3460_ = lean_ctor_get(v_x_3458_, 1);
                    v_tail_3461_ = lean_ctor_get(v_x_3458_, 2);
                    lean_inc(v_value_3460_);
                    lean_inc(v_key_3459_);
                    v___x_3462_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3462_, 0, v_key_3459_);
                    lean_ctor_set(v___x_3462_, 1, v_value_3460_);
                    v___x_3463_ = lean_array_push(v_x_3457_, v___x_3462_);
                    v_x_3457_ = v___x_3463_;
                    v_x_3458_ = v_tail_3461_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7___boxed(
    mut v_x_3465_: *mut LeanObject,
    mut v_x_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3467_: *mut LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_x_3465_, v_x_3466_);
    lean_dec(v_x_3466_);
    return v_res_3467_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(
    mut v_as_3468_: *mut LeanObject,
    mut v_i_3469_: usize,
    mut v_stop_3470_: usize,
    mut v_b_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: usize = 0;
    let mut v___x_3476_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3472_ = lean_usize_dec_eq(v_i_3469_, v_stop_3470_);
                if v___x_3472_ == 0 {
                    v___x_3473_ = lean_array_uget_borrowed(v_as_3468_, v_i_3469_);
                    v___x_3474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__7(v_b_3471_, v___x_3473_);
                    v___x_3475_ = 1usize;
                    v___x_3476_ = lean_usize_add(v_i_3469_, v___x_3475_);
                    v_i_3469_ = v___x_3476_;
                    v_b_3471_ = v___x_3474_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3471_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8___boxed(
    mut v_as_3478_: *mut LeanObject,
    mut v_i_3479_: *mut LeanObject,
    mut v_stop_3480_: *mut LeanObject,
    mut v_b_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3482_: usize = 0;
    let mut v_stop_boxed_3483_: usize = 0;
    let mut v_res_3484_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3482_ = lean_unbox_usize(v_i_3479_);
    lean_dec(v_i_3479_);
    v_stop_boxed_3483_ = lean_unbox_usize(v_stop_3480_);
    lean_dec(v_stop_3480_);
    v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_as_3478_, v_i_boxed_3482_, v_stop_boxed_3483_, v_b_3481_);
    lean_dec_ref(v_as_3478_);
    return v_res_3484_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(
    mut v_r_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_3486_ = lean_ctor_get(v_r_3485_, 0);
                v_stop_3487_ = lean_ctor_get(v_r_3485_, 1);
                v_isSharedCheck_3496_ = (!lean_is_exclusive(v_r_3485_)) as u8;
                if v_isSharedCheck_3496_ == 0 {
                    v___x_3489_ = v_r_3485_;
                    v_isShared_3490_ = v_isSharedCheck_3496_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_3487_);
                    lean_inc(v_start_3486_);
                    lean_dec(v_r_3485_);
                    v___x_3489_ = lean_box(0);
                    v_isShared_3490_ = v_isSharedCheck_3496_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3491_ = lean_nat_to_int(v_stop_3487_);
                v___x_3492_ = lean_int_neg(v___x_3491_);
                lean_dec(v___x_3491_);
                if v_isShared_3490_ == 0 {
                    lean_ctor_set(v___x_3489_, 1, v___x_3492_);
                    v___x_3494_ = v___x_3489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_start_3486_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3492_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(
    mut v_hi_3499_: *mut LeanObject,
    mut v_pivot_3500_: *mut LeanObject,
    mut v_as_3501_: *mut LeanObject,
    mut v_i_3502_: *mut LeanObject,
    mut v_k_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12384__overap_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3508_ = lean_nat_dec_lt(v_k_3503_, v_hi_3499_);
                if v___x_3508_ == 0 {
                    lean_dec(v_k_3503_);
                    lean_dec_ref(v_pivot_3500_);
                    v___x_3509_ = lean_array_fswap(v_as_3501_, v_i_3502_, v_hi_3499_);
                    v___x_3510_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3510_, 0, v_i_3502_);
                    lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                    return v___x_3510_;
                } else {
                    v___x_3511_ = lean_array_fget_borrowed(v_as_3501_, v_k_3503_);
                    v_fst_3512_ = lean_ctor_get(v___x_3511_, 0);
                    v_fst_3513_ = lean_ctor_get(v_pivot_3500_, 0);
                    v___f_3514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0;
                    v___f_3515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1;
                    lean_inc(v_fst_3512_);
                    v___x_3516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_3512_);
                    lean_inc(v_fst_3513_);
                    v___x_3517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__0(v_fst_3513_);
                    v___x_12384__overap_3518_ = l_lexOrd___redArg(v___f_3514_, v___f_3515_);
                    v___x_3519_ = lean_apply_2(v___x_12384__overap_3518_, v___x_3516_, v___x_3517_);
                    v___x_3520_ = (lean_unbox(v___x_3519_) as u8);
                    if v___x_3520_ == 0 {
                        if v___x_3508_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3521_ = lean_array_fswap(v_as_3501_, v_i_3502_, v_k_3503_);
                            v___x_3522_ = lean_unsigned_to_nat(1);
                            v___x_3523_ = lean_nat_add(v_i_3502_, v___x_3522_);
                            lean_dec(v_i_3502_);
                            v___x_3524_ = lean_nat_add(v_k_3503_, v___x_3522_);
                            lean_dec(v_k_3503_);
                            v_as_3501_ = v___x_3521_;
                            v_i_3502_ = v___x_3523_;
                            v_k_3503_ = v___x_3524_;
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
                v___x_3505_ = lean_unsigned_to_nat(1);
                v___x_3506_ = lean_nat_add(v_k_3503_, v___x_3505_);
                lean_dec(v_k_3503_);
                v_k_3503_ = v___x_3506_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___boxed(
    mut v_hi_3526_: *mut LeanObject,
    mut v_pivot_3527_: *mut LeanObject,
    mut v_as_3528_: *mut LeanObject,
    mut v_i_3529_: *mut LeanObject,
    mut v_k_3530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3531_: *mut LeanObject = core::ptr::null_mut();
    v_res_3531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_3526_, v_pivot_3527_, v_as_3528_, v_i_3529_, v_k_3530_);
    lean_dec(v_hi_3526_);
    return v_res_3531_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(
    mut v___f_3532_: *mut LeanObject,
    mut v___x_3533_: u8,
    mut v_x1_3534_: *mut LeanObject,
    mut v_x2_3535_: *mut LeanObject,
) -> u8 {
    let mut v_fst_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12647__overap_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: u8 = 0;
    v_fst_3536_ = lean_ctor_get(v_x1_3534_, 0);
    lean_inc(v_fst_3536_);
    lean_dec_ref(v_x1_3534_);
    v_fst_3537_ = lean_ctor_get(v_x2_3535_, 0);
    lean_inc(v_fst_3537_);
    lean_dec_ref(v_x2_3535_);
    v___f_3538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__0;
    v___f_3539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg___closed__1;
    lean_inc_ref(v___f_3532_);
    v___x_3540_ = lean_apply_1(v___f_3532_, v_fst_3536_);
    v___x_3541_ = lean_apply_1(v___f_3532_, v_fst_3537_);
    v___x_12647__overap_3542_ = l_lexOrd___redArg(v___f_3538_, v___f_3539_);
    v___x_3543_ = lean_apply_2(v___x_12647__overap_3542_, v___x_3540_, v___x_3541_);
    v___x_3544_ = (lean_unbox(v___x_3543_) as u8);
    if v___x_3544_ == 0 {
        return v___x_3533_;
    } else {
        let mut v___x_3545_: u8 = 0;
        v___x_3545_ = 0;
        return v___x_3545_;
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1___boxed(
    mut v___f_3546_: *mut LeanObject,
    mut v___x_3547_: *mut LeanObject,
    mut v_x1_3548_: *mut LeanObject,
    mut v_x2_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13878__boxed_3550_: u8 = 0;
    let mut v_res_3551_: u8 = 0;
    let mut v_r_3552_: *mut LeanObject = core::ptr::null_mut();
    v___x_13878__boxed_3550_ = (lean_unbox(v___x_3547_) as u8);
    v_res_3551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_3546_, v___x_13878__boxed_3550_, v_x1_3548_, v_x2_3549_);
    v_r_3552_ = lean_box((v_res_3551_) as usize);
    return v_r_3552_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(
    mut v_n_3554_: *mut LeanObject,
    mut v_as_3555_: *mut LeanObject,
    mut v_lo_3556_: *mut LeanObject,
    mut v_hi_3557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___f_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3569_ = lean_nat_dec_lt(v_lo_3556_, v_hi_3557_);
                if v___x_3569_ == 0 {
                    lean_dec(v_lo_3556_);
                    return v_as_3555_;
                } else {
                    v___f_3570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___closed__0;
                    v___x_3571_ = lean_nat_add(v_lo_3556_, v_hi_3557_);
                    v___x_3572_ = lean_unsigned_to_nat(1);
                    v_mid_3573_ = lean_nat_shiftr(v___x_3571_, v___x_3572_);
                    lean_dec(v___x_3571_);
                    v___x_3586_ = lean_array_fget_borrowed(v_as_3555_, v_mid_3573_);
                    v___x_3587_ = lean_array_fget_borrowed(v_as_3555_, v_lo_3556_);
                    lean_inc(v___x_3587_);
                    lean_inc(v___x_3586_);
                    v___x_3588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_3570_, v___x_3569_, v___x_3586_, v___x_3587_);
                    if v___x_3588_ == 0 {
                        v___y_3581_ = v_as_3555_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3589_ = lean_array_fswap(v_as_3555_, v_lo_3556_, v_mid_3573_);
                        v___y_3581_ = v___x_3589_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3560_ = lean_array_fget(v___y_3559_, v_hi_3557_);
                lean_inc_n(v_lo_3556_, 2);
                v___x_3561_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_3557_, v_pivot_3560_, v___y_3559_, v_lo_3556_, v_lo_3556_);
                v_fst_3562_ = lean_ctor_get(v___x_3561_, 0);
                lean_inc(v_fst_3562_);
                v_snd_3563_ = lean_ctor_get(v___x_3561_, 1);
                lean_inc(v_snd_3563_);
                lean_dec_ref(v___x_3561_);
                v___x_3564_ = lean_nat_dec_le(v_hi_3557_, v_fst_3562_);
                if v___x_3564_ == 0 {
                    v___x_3565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_3554_, v_snd_3563_, v_lo_3556_, v_fst_3562_);
                    v___x_3566_ = lean_unsigned_to_nat(1);
                    v___x_3567_ = lean_nat_add(v_fst_3562_, v___x_3566_);
                    lean_dec(v_fst_3562_);
                    v_as_3555_ = v___x_3565_;
                    v_lo_3556_ = v___x_3567_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_3562_);
                    lean_dec(v_lo_3556_);
                    return v_snd_3563_;
                }
            }
            2 => {
                v___x_3576_ = lean_array_fget_borrowed(v___y_3575_, v_mid_3573_);
                v___x_3577_ = lean_array_fget_borrowed(v___y_3575_, v_hi_3557_);
                lean_inc(v___x_3577_);
                lean_inc(v___x_3576_);
                v___x_3578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_3570_, v___x_3569_, v___x_3576_, v___x_3577_);
                if v___x_3578_ == 0 {
                    lean_dec(v_mid_3573_);
                    v___y_3559_ = v___y_3575_;
                    state = 1;
                    continue;
                } else {
                    v___x_3579_ = lean_array_fswap(v___y_3575_, v_mid_3573_, v_hi_3557_);
                    lean_dec(v_mid_3573_);
                    v___y_3559_ = v___x_3579_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3582_ = lean_array_fget_borrowed(v___y_3581_, v_hi_3557_);
                v___x_3583_ = lean_array_fget_borrowed(v___y_3581_, v_lo_3556_);
                lean_inc(v___x_3583_);
                lean_inc(v___x_3582_);
                v___x_3584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___lam__1(v___f_3570_, v___x_3569_, v___x_3582_, v___x_3583_);
                if v___x_3584_ == 0 {
                    v___y_3575_ = v___y_3581_;
                    state = 2;
                    continue;
                } else {
                    v___x_3585_ = lean_array_fswap(v___y_3581_, v_lo_3556_, v_hi_3557_);
                    v___y_3575_ = v___x_3585_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg___boxed(
    mut v_n_3590_: *mut LeanObject,
    mut v_as_3591_: *mut LeanObject,
    mut v_lo_3592_: *mut LeanObject,
    mut v_hi_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3594_: *mut LeanObject = core::ptr::null_mut();
    v_res_3594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_3590_, v_as_3591_, v_lo_3592_, v_hi_3593_);
    lean_dec(v_hi_3593_);
    lean_dec(v_n_3590_);
    return v_res_3594_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3601_ = lean_box(0);
    v___x_3602_ = lean_unsigned_to_nat(16);
    v___x_3603_ = lean_mk_array(v___x_3602_, v___x_3601_);
    return v___x_3603_;
}
pub unsafe fn _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3604_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4_once
        ),
        _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__4,
    );
    v___x_3605_ = lean_unsigned_to_nat(0);
    v___x_3606_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3606_, 0, v___x_3605_);
    lean_ctor_set(v___x_3606_, 1, v___x_3604_);
    return v___x_3606_;
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(
    mut v_stx_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
    mut v___y_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3614_: usize = 0;
    let mut v___x_3615_: usize = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v_unused_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v___y_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: u8 = 0;
    let mut v___y_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v___y_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: usize = 0;
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: usize = 0;
    let mut v___x_3672_: usize = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v_ref_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3691_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: u8 = 0;
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_categories_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kinds_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kinds_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: u8 = 0;
    let mut v_infoState_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3743_: u8 = 0;
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3687_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1(v___y_3608_, v___y_3609_);
                v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
                v_isSharedCheck_3744_ = (!lean_is_exclusive(v___x_3687_)) as u8;
                if v_isSharedCheck_3744_ == 0 {
                    v___x_3690_ = v___x_3687_;
                    v_isShared_3691_ = v_isSharedCheck_3744_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_a_3688_);
                    lean_dec(v___x_3687_);
                    v___x_3690_ = lean_box(0);
                    v_isShared_3691_ = v_isSharedCheck_3744_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v_sz_3614_ = lean_array_size(v___y_3613_);
                v___x_3615_ = 0usize;
                v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__5(v___y_3613_, v_sz_3614_, v___x_3615_, v___y_3612_, v___y_3608_, v___y_3609_);
                lean_dec_ref(v___y_3613_);
                if lean_obj_tag(v___x_3616_) == 0 {
                    v_isSharedCheck_3624_ = (!lean_is_exclusive(v___x_3616_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v_unused_3625_ = lean_ctor_get(v___x_3616_, 0);
                        lean_dec(v_unused_3625_);
                        v___x_3618_ = v___x_3616_;
                        v_isShared_3619_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_3616_);
                        v___x_3618_ = lean_box(0);
                        v_isShared_3619_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3626_ = lean_ctor_get(v___x_3616_, 0);
                    v_isSharedCheck_3633_ = (!lean_is_exclusive(v___x_3616_)) as u8;
                    if v_isSharedCheck_3633_ == 0 {
                        v___x_3628_ = v___x_3616_;
                        v_isShared_3629_ = v_isSharedCheck_3633_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3626_);
                        lean_dec(v___x_3616_);
                        v___x_3628_ = lean_box(0);
                        v_isShared_3629_ = v_isSharedCheck_3633_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3620_ = lean_box(0);
                if v_isShared_3619_ == 0 {
                    lean_ctor_set(v___x_3618_, 0, v___x_3620_);
                    v___x_3622_ = v___x_3618_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3622_;
            }
            4 => {
                if v_isShared_3629_ == 0 {
                    v___x_3631_ = v___x_3628_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3631_;
            }
            6 => {
                v___x_3640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v___y_3637_, v___y_3638_, v___y_3636_, v___y_3639_);
                lean_dec(v___y_3639_);
                lean_dec(v___y_3637_);
                v___y_3612_ = v___y_3635_;
                v___y_3613_ = v___x_3640_;
                state = 1;
                continue;
            }
            7 => {
                v___x_3647_ = lean_nat_dec_le(v___y_3646_, v___y_3643_);
                if v___x_3647_ == 0 {
                    lean_dec(v___y_3643_);
                    lean_inc(v___y_3646_);
                    v___y_3635_ = v___y_3642_;
                    v___y_3636_ = v___y_3646_;
                    v___y_3637_ = v___y_3644_;
                    v___y_3638_ = v___y_3645_;
                    v___y_3639_ = v___y_3646_;
                    state = 6;
                    continue;
                } else {
                    v___y_3635_ = v___y_3642_;
                    v___y_3636_ = v___y_3646_;
                    v___y_3637_ = v___y_3644_;
                    v___y_3638_ = v___y_3645_;
                    v___y_3639_ = v___y_3643_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_n(v___y_3649_, 2);
                v___x_3651_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3651_, 0, v___y_3649_);
                lean_ctor_set(v___x_3651_, 1, v___y_3649_);
                v___x_3652_ = lean_array_get_size(v___y_3650_);
                v___x_3653_ = lean_nat_dec_eq(v___x_3652_, v___y_3649_);
                if v___x_3653_ == 0 {
                    v___x_3654_ = lean_unsigned_to_nat(1);
                    v___x_3655_ = lean_nat_sub(v___x_3652_, v___x_3654_);
                    v___x_3656_ = lean_nat_dec_le(v___y_3649_, v___x_3655_);
                    if v___x_3656_ == 0 {
                        lean_dec(v___y_3649_);
                        lean_inc(v___x_3655_);
                        v___y_3642_ = v___x_3651_;
                        v___y_3643_ = v___x_3655_;
                        v___y_3644_ = v___x_3652_;
                        v___y_3645_ = v___y_3650_;
                        v___y_3646_ = v___x_3655_;
                        state = 7;
                        continue;
                    } else {
                        v___y_3642_ = v___x_3651_;
                        v___y_3643_ = v___x_3655_;
                        v___y_3644_ = v___x_3652_;
                        v___y_3645_ = v___y_3650_;
                        v___y_3646_ = v___y_3649_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___y_3649_);
                    v___y_3612_ = v___x_3651_;
                    v___y_3613_ = v___y_3650_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                if lean_obj_tag(v___y_3660_) == 0 {
                    lean_dec_ref_known(v___y_3660_, 1);
                    v___x_3661_ = lean_st_ref_get(v___y_3658_);
                    lean_dec(v___y_3658_);
                    v_size_3662_ = lean_ctor_get(v___x_3661_, 0);
                    lean_inc(v_size_3662_);
                    v_buckets_3663_ = lean_ctor_get(v___x_3661_, 1);
                    lean_inc_ref(v_buckets_3663_);
                    lean_dec(v___x_3661_);
                    v___x_3664_ = lean_mk_empty_array_with_capacity(v_size_3662_);
                    lean_dec(v_size_3662_);
                    v___x_3665_ = lean_array_get_size(v_buckets_3663_);
                    v___x_3666_ = lean_nat_dec_lt(v___y_3659_, v___x_3665_);
                    if v___x_3666_ == 0 {
                        lean_dec_ref(v_buckets_3663_);
                        v___y_3649_ = v___y_3659_;
                        v___y_3650_ = v___x_3664_;
                        state = 8;
                        continue;
                    } else {
                        v___x_3667_ = lean_nat_dec_le(v___x_3665_, v___x_3665_);
                        if v___x_3667_ == 0 {
                            if v___x_3666_ == 0 {
                                lean_dec_ref(v_buckets_3663_);
                                v___y_3649_ = v___y_3659_;
                                v___y_3650_ = v___x_3664_;
                                state = 8;
                                continue;
                            } else {
                                v___x_3668_ = 0usize;
                                v___x_3669_ = lean_usize_of_nat(v___x_3665_);
                                v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_buckets_3663_, v___x_3668_, v___x_3669_, v___x_3664_);
                                lean_dec_ref(v_buckets_3663_);
                                v___y_3649_ = v___y_3659_;
                                v___y_3650_ = v___x_3670_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_3671_ = 0usize;
                            v___x_3672_ = lean_usize_of_nat(v___x_3665_);
                            v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__8(v_buckets_3663_, v___x_3671_, v___x_3672_, v___x_3664_);
                            lean_dec_ref(v_buckets_3663_);
                            v___y_3649_ = v___y_3659_;
                            v___y_3650_ = v___x_3673_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3659_);
                    lean_dec(v___y_3658_);
                    v_a_3674_ = lean_ctor_get(v___y_3660_, 0);
                    v_isSharedCheck_3686_ = (!lean_is_exclusive(v___y_3660_)) as u8;
                    if v_isSharedCheck_3686_ == 0 {
                        v___x_3676_ = v___y_3660_;
                        v_isShared_3677_ = v_isSharedCheck_3686_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3674_);
                        lean_dec(v___y_3660_);
                        v___x_3676_ = lean_box(0);
                        v_isShared_3677_ = v_isSharedCheck_3686_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v_ref_3678_ = lean_ctor_get(v___y_3608_, 7);
                v___x_3679_ = lean_io_error_to_string(v_a_3674_);
                v___x_3680_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3680_, 0, v___x_3679_);
                v___x_3681_ = l_Lean_MessageData_ofFormat(v___x_3680_);
                lean_inc(v_ref_3678_);
                v___x_3682_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3682_, 0, v_ref_3678_);
                lean_ctor_set(v___x_3682_, 1, v___x_3681_);
                if v_isShared_3677_ == 0 {
                    lean_ctor_set(v___x_3676_, 0, v___x_3682_);
                    v___x_3684_ = v___x_3676_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3684_;
            }
            12 => {
                v___x_3692_ = lean_st_ref_get(v___y_3609_);
                v___x_3740_ = l_Lean_Linter_Extra_linter_extra_unreachableTactic;
                v___x_3741_ = l_Lean_Linter_getLinterValueExtra(v___x_3740_, v_a_3688_);
                lean_dec(v_a_3688_);
                if v___x_3741_ == 0 {
                    lean_dec(v___x_3692_);
                    v___y_3694_ = v___x_3741_;
                    state = 13;
                    continue;
                } else {
                    v_infoState_3742_ = lean_ctor_get(v___x_3692_, 8);
                    lean_inc_ref(v_infoState_3742_);
                    lean_dec(v___x_3692_);
                    v_enabled_3743_ = lean_ctor_get_uint8(
                        v_infoState_3742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref(v_infoState_3742_);
                    v___y_3694_ = v_enabled_3743_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_3694_ == 0 {
                    lean_dec(v_stx_3607_);
                    v___x_3695_ = lean_box(0);
                    if v_isShared_3691_ == 0 {
                        lean_ctor_set(v___x_3690_, 0, v___x_3695_);
                        v___x_3697_ = v___x_3690_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
                        v___x_3697_ = v_reuseFailAlloc_3698_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_3699_ = lean_st_ref_get(v___y_3609_);
                    v_messages_3700_ = lean_ctor_get(v___x_3699_, 1);
                    lean_inc_ref(v_messages_3700_);
                    lean_dec(v___x_3699_);
                    v___x_3701_ = l_Lean_MessageLog_hasErrors(v_messages_3700_);
                    lean_dec_ref(v_messages_3700_);
                    if v___x_3701_ == 0 {
                        v___x_3702_ = lean_st_ref_get(v___y_3609_);
                        v_env_3703_ = lean_ctor_get(v___x_3702_, 0);
                        lean_inc_ref(v_env_3703_);
                        lean_dec(v___x_3702_);
                        v___x_3704_ = l_Lean_Parser_parserExtension;
                        v_ext_3705_ = lean_ctor_get(v___x_3704_, 1);
                        v_toEnvExtension_3706_ = lean_ctor_get(v_ext_3705_, 0);
                        v_asyncMode_3707_ = lean_ctor_get(v_toEnvExtension_3706_, 2);
                        v___x_3708_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
                        v___x_3709_ = l_Lean_ScopedEnvExtension_getState___redArg(
                            v___x_3708_,
                            v___x_3704_,
                            v_env_3703_,
                            v_asyncMode_3707_,
                        );
                        v_categories_3710_ = lean_ctor_get(v___x_3709_, 2);
                        lean_inc_ref(v_categories_3710_);
                        lean_dec(v___x_3709_);
                        v___x_3711_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__1;
                        v___x_3712_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_3710_, v___x_3711_);
                        if lean_obj_tag(v___x_3712_) == 0 {
                            lean_dec_ref(v_categories_3710_);
                            lean_dec(v_stx_3607_);
                            v___x_3713_ = lean_box(0);
                            if v_isShared_3691_ == 0 {
                                lean_ctor_set(v___x_3690_, 0, v___x_3713_);
                                v___x_3715_ = v___x_3690_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
                                v___x_3715_ = v_reuseFailAlloc_3716_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_val_3717_ = lean_ctor_get(v___x_3712_, 0);
                            lean_inc(v_val_3717_);
                            lean_dec_ref_known(v___x_3712_, 1);
                            v___x_3718_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__3;
                            v___x_3719_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_categories_3710_, v___x_3718_);
                            lean_dec_ref(v_categories_3710_);
                            if lean_obj_tag(v___x_3719_) == 0 {
                                lean_dec(v_val_3717_);
                                lean_dec(v_stx_3607_);
                                v___x_3720_ = lean_box(0);
                                if v_isShared_3691_ == 0 {
                                    lean_ctor_set(v___x_3690_, 0, v___x_3720_);
                                    v___x_3722_ = v___x_3690_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
                                    v___x_3722_ = v_reuseFailAlloc_3723_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_3690_);
                                v_val_3724_ = lean_ctor_get(v___x_3719_, 0);
                                lean_inc(v_val_3724_);
                                lean_dec_ref_known(v___x_3719_, 1);
                                v___x_3725_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__4___redArg(v___y_3609_);
                                v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
                                lean_inc(v_a_3726_);
                                lean_dec_ref(v___x_3725_);
                                v___x_3727_ = lean_unsigned_to_nat(0);
                                v___x_3728_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5_once), _init_l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___closed__5);
                                v___x_3729_ = lean_st_mk_ref(v___x_3728_);
                                v___x_3730_ =
                                    l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef;
                                v___x_3731_ = lean_st_ref_get(v___x_3730_);
                                v_kinds_3732_ = lean_ctor_get(v_val_3717_, 1);
                                lean_inc_ref(v_kinds_3732_);
                                lean_dec(v_val_3717_);
                                v_kinds_3733_ = lean_ctor_get(v_val_3724_, 1);
                                lean_inc_ref(v_kinds_3733_);
                                lean_dec(v_val_3724_);
                                v___x_3734_ = l_Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10(v_kinds_3732_, v_kinds_3733_, v___y_3694_, v___x_3731_, v_stx_3607_, v___x_3729_);
                                lean_dec(v___x_3731_);
                                lean_dec_ref(v_kinds_3733_);
                                lean_dec_ref(v_kinds_3732_);
                                if lean_obj_tag(v___x_3734_) == 0 {
                                    lean_dec_ref_known(v___x_3734_, 1);
                                    v___x_3735_ =
                                        l_Lean_Linter_Extra_UnreachableTactic_eraseUsedTacticsList(
                                            v_a_3726_,
                                            v___x_3729_,
                                        );
                                    v___y_3658_ = v___x_3729_;
                                    v___y_3659_ = v___x_3727_;
                                    v___y_3660_ = v___x_3735_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec(v_a_3726_);
                                    v___y_3658_ = v___x_3729_;
                                    v___y_3659_ = v___x_3727_;
                                    v___y_3660_ = v___x_3734_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_stx_3607_);
                        v___x_3736_ = lean_box(0);
                        if v_isShared_3691_ == 0 {
                            lean_ctor_set(v___x_3690_, 0, v___x_3736_);
                            v___x_3738_ = v___x_3690_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
                            v___x_3738_ = v_reuseFailAlloc_3739_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            14 => {
                return v___x_3697_;
            }
            15 => {
                return v___x_3715_;
            }
            16 => {
                return v___x_3722_;
            }
            17 => {
                return v___x_3738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0___boxed(
    mut v_stx_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3749_: *mut LeanObject = core::ptr::null_mut();
    v_res_3749_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter___lam__0(
        v_stx_3745_,
        v___y_3746_,
        v___y_3747_,
    );
    lean_dec(v___y_3747_);
    lean_dec_ref(v___y_3746_);
    return v_res_3749_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(
    mut v_o_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    v___x_3769_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___redArg(v_o_3765_, v___y_3767_);
    return v___x_3769_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1___boxed(
    mut v_o_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
    mut v___y_3772_: *mut LeanObject,
    mut v___y_3773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3774_: *mut LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__1_spec__1(v_o_3770_, v___y_3771_, v___y_3772_);
    lean_dec(v___y_3772_);
    lean_dec_ref(v___y_3771_);
    return v_res_3774_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(
    mut v_00_u03b2_3775_: *mut LeanObject,
    mut v_x_3776_: *mut LeanObject,
    mut v_x_3777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    v___x_3778_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___redArg(v_x_3776_, v_x_3777_);
    return v___x_3778_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3___boxed(
    mut v_00_u03b2_3779_: *mut LeanObject,
    mut v_x_3780_: *mut LeanObject,
    mut v_x_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3782_: *mut LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3(v_00_u03b2_3779_, v_x_3780_, v_x_3781_);
    lean_dec(v_x_3781_);
    lean_dec_ref(v_x_3780_);
    return v_res_3782_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(
    mut v_n_3783_: *mut LeanObject,
    mut v_as_3784_: *mut LeanObject,
    mut v_lo_3785_: *mut LeanObject,
    mut v_hi_3786_: *mut LeanObject,
    mut v_w_3787_: *mut LeanObject,
    mut v_hlo_3788_: *mut LeanObject,
    mut v_hhi_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    v___x_3790_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___redArg(v_n_3783_, v_as_3784_, v_lo_3785_, v_hi_3786_);
    return v___x_3790_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6___boxed(
    mut v_n_3791_: *mut LeanObject,
    mut v_as_3792_: *mut LeanObject,
    mut v_lo_3793_: *mut LeanObject,
    mut v_hi_3794_: *mut LeanObject,
    mut v_w_3795_: *mut LeanObject,
    mut v_hlo_3796_: *mut LeanObject,
    mut v_hhi_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3798_: *mut LeanObject = core::ptr::null_mut();
    v_res_3798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6(v_n_3791_, v_as_3792_, v_lo_3793_, v_hi_3794_, v_w_3795_, v_hlo_3796_, v_hhi_3797_);
    lean_dec(v_hi_3794_);
    lean_dec(v_n_3791_);
    return v_res_3798_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(
    mut v_00_u03b2_3799_: *mut LeanObject,
    mut v_x_3800_: *mut LeanObject,
    mut v_x_3801_: *mut LeanObject,
) -> u8 {
    let mut v___x_3802_: u8 = 0;
    v___x_3802_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___redArg(v_x_3800_, v_x_3801_);
    return v___x_3802_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9___boxed(
    mut v_00_u03b2_3803_: *mut LeanObject,
    mut v_x_3804_: *mut LeanObject,
    mut v_x_3805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3806_: u8 = 0;
    let mut v_r_3807_: *mut LeanObject = core::ptr::null_mut();
    v_res_3806_ = l_Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9(v_00_u03b2_3803_, v_x_3804_, v_x_3805_);
    lean_dec(v_x_3805_);
    lean_dec_ref(v_x_3804_);
    v_r_3807_ = lean_box((v_res_3806_) as usize);
    return v_r_3807_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(
    mut v_00_u03b2_3808_: *mut LeanObject,
    mut v_x_3809_: *mut LeanObject,
    mut v_x_3810_: usize,
    mut v_x_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___redArg(v_x_3809_, v_x_3810_, v_x_3811_);
    return v___x_3812_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5___boxed(
    mut v_00_u03b2_3813_: *mut LeanObject,
    mut v_x_3814_: *mut LeanObject,
    mut v_x_3815_: *mut LeanObject,
    mut v_x_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14334__boxed_3817_: usize = 0;
    let mut v_res_3818_: *mut LeanObject = core::ptr::null_mut();
    v_x_14334__boxed_3817_ = lean_unbox_usize(v_x_3815_);
    lean_dec(v_x_3815_);
    v_res_3818_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5(v_00_u03b2_3813_, v_x_3814_, v_x_14334__boxed_3817_, v_x_3816_);
    lean_dec(v_x_3816_);
    lean_dec_ref(v_x_3814_);
    return v_res_3818_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(
    mut v_n_3819_: *mut LeanObject,
    mut v_lo_3820_: *mut LeanObject,
    mut v_hi_3821_: *mut LeanObject,
    mut v_hhi_3822_: *mut LeanObject,
    mut v_pivot_3823_: *mut LeanObject,
    mut v_as_3824_: *mut LeanObject,
    mut v_i_3825_: *mut LeanObject,
    mut v_k_3826_: *mut LeanObject,
    mut v_ilo_3827_: *mut LeanObject,
    mut v_ik_3828_: *mut LeanObject,
    mut v_w_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___redArg(v_hi_3821_, v_pivot_3823_, v_as_3824_, v_i_3825_, v_k_3826_);
    return v___x_3830_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9___boxed(
    mut v_n_3831_: *mut LeanObject,
    mut v_lo_3832_: *mut LeanObject,
    mut v_hi_3833_: *mut LeanObject,
    mut v_hhi_3834_: *mut LeanObject,
    mut v_pivot_3835_: *mut LeanObject,
    mut v_as_3836_: *mut LeanObject,
    mut v_i_3837_: *mut LeanObject,
    mut v_k_3838_: *mut LeanObject,
    mut v_ilo_3839_: *mut LeanObject,
    mut v_ik_3840_: *mut LeanObject,
    mut v_w_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_res_3842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__6_spec__9(v_n_3831_, v_lo_3832_, v_hi_3833_, v_hhi_3834_, v_pivot_3835_, v_as_3836_, v_i_3837_, v_k_3838_, v_ilo_3839_, v_ik_3840_, v_w_3841_);
    lean_dec(v_hi_3833_);
    lean_dec(v_lo_3832_);
    lean_dec(v_n_3831_);
    return v_res_3842_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(
    mut v_00_u03b2_3843_: *mut LeanObject,
    mut v_x_3844_: *mut LeanObject,
    mut v_x_3845_: usize,
    mut v_x_3846_: *mut LeanObject,
) -> u8 {
    let mut v___x_3847_: u8 = 0;
    v___x_3847_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___redArg(v_x_3844_, v_x_3845_, v_x_3846_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13___boxed(
    mut v_00_u03b2_3848_: *mut LeanObject,
    mut v_x_3849_: *mut LeanObject,
    mut v_x_3850_: *mut LeanObject,
    mut v_x_3851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_14347__boxed_3852_: usize = 0;
    let mut v_res_3853_: u8 = 0;
    let mut v_r_3854_: *mut LeanObject = core::ptr::null_mut();
    v_x_14347__boxed_3852_ = lean_unbox_usize(v_x_3850_);
    lean_dec(v_x_3850_);
    v_res_3853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13(v_00_u03b2_3848_, v_x_3849_, v_x_14347__boxed_3852_, v_x_3851_);
    lean_dec(v_x_3851_);
    lean_dec_ref(v_x_3849_);
    v_r_3854_ = lean_box((v_res_3853_) as usize);
    return v_r_3854_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15(
    mut v_00_u03b2_3855_: *mut LeanObject,
    mut v_m_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
    mut v_b_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15___redArg(v_m_3856_, v_a_3857_, v_b_3858_);
    return v___x_3859_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(
    mut v_00_u03b2_3860_: *mut LeanObject,
    mut v_keys_3861_: *mut LeanObject,
    mut v_vals_3862_: *mut LeanObject,
    mut v_heq_3863_: *mut LeanObject,
    mut v_i_3864_: *mut LeanObject,
    mut v_k_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    v___x_3866_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___redArg(v_keys_3861_, v_vals_3862_, v_i_3864_, v_k_3865_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_3867_: *mut LeanObject,
    mut v_keys_3868_: *mut LeanObject,
    mut v_vals_3869_: *mut LeanObject,
    mut v_heq_3870_: *mut LeanObject,
    mut v_i_3871_: *mut LeanObject,
    mut v_k_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3873_: *mut LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__3_spec__5_spec__8(v_00_u03b2_3867_, v_keys_3868_, v_vals_3869_, v_heq_3870_, v_i_3871_, v_k_3872_);
    lean_dec(v_k_3872_);
    lean_dec_ref(v_vals_3869_);
    lean_dec_ref(v_keys_3868_);
    return v_res_3873_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(
    mut v_00_u03b2_3874_: *mut LeanObject,
    mut v_keys_3875_: *mut LeanObject,
    mut v_vals_3876_: *mut LeanObject,
    mut v_heq_3877_: *mut LeanObject,
    mut v_i_3878_: *mut LeanObject,
    mut v_k_3879_: *mut LeanObject,
) -> u8 {
    let mut v___x_3880_: u8 = 0;
    v___x_3880_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___redArg(v_keys_3875_, v_i_3878_, v_k_3879_);
    return v___x_3880_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16___boxed(
    mut v_00_u03b2_3881_: *mut LeanObject,
    mut v_keys_3882_: *mut LeanObject,
    mut v_vals_3883_: *mut LeanObject,
    mut v_heq_3884_: *mut LeanObject,
    mut v_i_3885_: *mut LeanObject,
    mut v_k_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut LeanObject = core::ptr::null_mut();
    v_res_3887_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__9_spec__13_spec__16(v_00_u03b2_3881_, v_keys_3882_, v_vals_3883_, v_heq_3884_, v_i_3885_, v_k_3886_);
    lean_dec(v_k_3886_);
    lean_dec_ref(v_vals_3883_);
    lean_dec_ref(v_keys_3882_);
    v_r_3888_ = lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19(
    mut v_00_u03b2_3889_: *mut LeanObject,
    mut v_data_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    v___x_3891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19___redArg(v_data_3890_);
    return v___x_3891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20(
    mut v_00_u03b2_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_b_3894_: *mut LeanObject,
    mut v_x_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    v___x_3896_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__20___redArg(v_a_3893_, v_b_3894_, v_x_3895_);
    return v___x_3896_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(
    mut v_msgData_3897_: *mut LeanObject,
    mut v___y_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    v___x_3901_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___redArg(v_msgData_3897_, v___y_3899_);
    return v___x_3901_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19___boxed(
    mut v_msgData_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3906_: *mut LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__2_spec__3_spec__5_spec__13_spec__19(v_msgData_3902_, v___y_3903_, v___y_3904_);
    lean_dec(v___y_3904_);
    lean_dec_ref(v___y_3903_);
    return v_res_3906_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21(
    mut v_00_u03b2_3907_: *mut LeanObject,
    mut v_i_3908_: *mut LeanObject,
    mut v_source_3909_: *mut LeanObject,
    mut v_target_3910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21___redArg(v_i_3908_, v_source_3909_, v_target_3910_);
    return v___x_3911_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25(
    mut v_00_u03b2_3912_: *mut LeanObject,
    mut v_x_3913_: *mut LeanObject,
    mut v_x_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_Extra_UnreachableTactic_getTactics___at___00Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter_spec__10_spec__15_spec__19_spec__21_spec__25___redArg(v_x_3913_, v_x_3914_);
    return v___x_3915_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    v___x_3917_ = l_Lean_Linter_Extra_UnreachableTactic_unreachableTacticLinter;
    v___x_3918_ = l_Lean_Elab_Command_addLinter(v___x_3917_);
    return v___x_3918_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2____boxed(
    mut v_a_3919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3920_: *mut LeanObject = core::ptr::null_mut();
    v_res_3920_ = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
    return v_res_3920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Extra_UnreachableTactic(
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
    res = runtime_initialize_Lean_Parser_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_3804698830____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_linter_extra_unreachableTactic = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unreachableTactic);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_949854657____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_Extra_UnreachableTactic_ignoreTacticKindsRef);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnreachableTactic_0__Lean_Linter_Extra_UnreachableTactic_initFn_00___x40_Lean_Linter_Extra_UnreachableTactic_1366347041____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Extra_UnreachableTactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Extra_UnreachableTactic(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Parser_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
}
