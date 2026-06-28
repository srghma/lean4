// Lean compiler output
// Module: Lean.Linter.Extra.DupNamespace
// Imports: Lean.Elab.Command Lean.Linter.Basic
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_zipWith___at___00List_zip_spec__0;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_find_x3f, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_Name_mkStr6, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_components;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::{l_Lean_FileMap_ofPosition, l_Lean_FileMap_toPosition};
use crate::r#gen::Lean::DeclarationRange::l_Lean_declRangeExt;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_PersistentEnvExtension_getState___redArg;
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
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instInhabitedRange_default, l_Lean_Syntax_ofRange,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_forInStep___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_le,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 117, 112, 78, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,8383467597245298465 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,9114931515398833764 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 100, 117, 112, 108, 105, 99, 97, 116, 101, 100, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,8412578185445384546 as *mut LeanObject] };
static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,9890441027862740329 as *mut LeanObject] };
pub static l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,14695736980110498764 as *mut LeanObject] };
static mut l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 120, 112, 111, 114, 116, 0],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value
) as *mut LeanObject;
static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1:
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
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2:
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
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value:
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
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value
        ) as *mut LeanObject,
        9165173072911943942 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [84, 104, 101, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [39, 32, 105, 115, 32, 100, 117, 112, 108, 105, 99, 97, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value:
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
    m_fun: l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value:
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
    m_fun: l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value:
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
        l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value: LeanStringObject<
    19,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        68, 117, 112, 78, 97, 109, 101, 115, 112, 97, 99, 101, 76, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value)
        as *mut LeanObject;
static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,14342914028213736627 as *mut LeanObject] };
static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value)
            as *mut LeanObject,
        16521423970400063881 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value) as *mut LeanObject,10265473659350402348 as *mut LeanObject] };
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(
    mut v_name_961_: *mut LeanObject,
    mut v_decl_962_: *mut LeanObject,
    mut v_ref_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v_unused_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_984_: u8 = 0;
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_965_ = lean_ctor_get(v_decl_962_, 0);
                v_descr_966_ = lean_ctor_get(v_decl_962_, 1);
                v_deprecation_x3f_967_ = lean_ctor_get(v_decl_962_, 2);
                v___x_968_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_969_ = (lean_unbox(v_defValue_965_) as u8);
                lean_ctor_set_uint8(v___x_968_, 0 as u32, v___x_969_);
                lean_inc(v_deprecation_x3f_967_);
                lean_inc_ref(v_descr_966_);
                lean_inc_n(v_name_961_, 2);
                v___x_970_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_970_, 0, v_name_961_);
                lean_ctor_set(v___x_970_, 1, v_ref_963_);
                lean_ctor_set(v___x_970_, 2, v___x_968_);
                lean_ctor_set(v___x_970_, 3, v_descr_966_);
                lean_ctor_set(v___x_970_, 4, v_deprecation_x3f_967_);
                v___x_971_ = lean_register_option(v_name_961_, v___x_970_);
                if lean_obj_tag(v___x_971_) == 0 {
                    v_isSharedCheck_979_ = (!lean_is_exclusive(v___x_971_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v_unused_980_ = lean_ctor_get(v___x_971_, 0);
                        lean_dec(v_unused_980_);
                        v___x_973_ = v___x_971_;
                        v_isShared_974_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_971_);
                        v___x_973_ = lean_box(0);
                        v_isShared_974_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_961_);
                    v_a_981_ = lean_ctor_get(v___x_971_, 0);
                    v_isSharedCheck_988_ = (!lean_is_exclusive(v___x_971_)) as u8;
                    if v_isSharedCheck_988_ == 0 {
                        v___x_983_ = v___x_971_;
                        v_isShared_984_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_981_);
                        lean_dec(v___x_971_);
                        v___x_983_ = lean_box(0);
                        v_isShared_984_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_965_);
                v___x_975_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_975_, 0, v_name_961_);
                lean_ctor_set(v___x_975_, 1, v_defValue_965_);
                if v_isShared_974_ == 0 {
                    lean_ctor_set(v___x_973_, 0, v___x_975_);
                    v___x_977_ = v___x_973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_977_;
            }
            3 => {
                if v_isShared_984_ == 0 {
                    v___x_986_ = v___x_983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
                    v___x_986_ = v_reuseFailAlloc_987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_989_: *mut LeanObject,
    mut v_decl_990_: *mut LeanObject,
    mut v_ref_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_993_: *mut LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(v_name_989_, v_decl_990_, v_ref_991_);
    lean_dec_ref(v_decl_990_);
    return v_res_993_;
}
pub unsafe fn l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_1018_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_;
    v___x_1019_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_;
    v___x_1020_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_;
    v___x_1021_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(v___x_1018_, v___x_1019_, v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4____boxed(
    mut v_a_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1023_: *mut LeanObject = core::ptr::null_mut();
    v_res_1023_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_();
    return v_res_1023_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0(
    mut v_toPure_1024_: *mut LeanObject,
    mut v_____do__lift_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v_a_1026_ = lean_ctor_get(v_____do__lift_1025_, 0);
    lean_inc(v_a_1026_);
    lean_dec_ref(v_____do__lift_1025_);
    v___x_1027_ = lean_apply_2(v_toPure_1024_, lean_box(0), v_a_1026_);
    return v___x_1027_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1(
    mut v_toPure_1028_: *mut LeanObject,
    mut v_____s_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = lean_apply_2(v_toPure_1028_, lean_box(0), v_____s_1029_);
    return v___x_1030_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(
    mut v_fm_1031_: *mut LeanObject,
    mut v_pos_1032_: *mut LeanObject,
    mut v_toPure_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_b_1035_: *mut LeanObject,
    mut v_c_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_range_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v_pos_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_1037_ = lean_ctor_get(v_b_1035_, 0);
                v_selectionRange_1038_ = lean_ctor_get(v_b_1035_, 1);
                v_isSharedCheck_1060_ = (!lean_is_exclusive(v_b_1035_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1040_ = v_b_1035_;
                    v_isShared_1041_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_selectionRange_1038_);
                    lean_inc(v_range_1037_);
                    lean_dec(v_b_1035_);
                    v___x_1040_ = lean_box(0);
                    v_isShared_1041_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_pos_1042_ = lean_ctor_get(v_range_1037_, 0);
                lean_inc_ref(v_pos_1042_);
                lean_dec_ref(v_range_1037_);
                v___x_1043_ = l_Lean_FileMap_ofPosition(v_fm_1031_, v_pos_1042_);
                v___x_1044_ = lean_nat_dec_le(v_pos_1032_, v___x_1043_);
                lean_dec(v___x_1043_);
                if v___x_1044_ == 0 {
                    lean_del_object(v___x_1040_);
                    lean_dec_ref(v_selectionRange_1038_);
                    lean_dec(v_a_1034_);
                    v___x_1045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1045_, 0, v_c_1036_);
                    v___x_1046_ = lean_apply_2(v_toPure_1033_, lean_box(0), v___x_1045_);
                    return v___x_1046_;
                } else {
                    v_pos_1047_ = lean_ctor_get(v_selectionRange_1038_, 0);
                    lean_inc_ref(v_pos_1047_);
                    v_endPos_1048_ = lean_ctor_get(v_selectionRange_1038_, 2);
                    lean_inc_ref(v_endPos_1048_);
                    lean_dec_ref(v_selectionRange_1038_);
                    v___x_1049_ = l_Lean_FileMap_ofPosition(v_fm_1031_, v_pos_1047_);
                    v___x_1050_ = l_Lean_FileMap_ofPosition(v_fm_1031_, v_endPos_1048_);
                    if v_isShared_1041_ == 0 {
                        lean_ctor_set(v___x_1040_, 1, v___x_1050_);
                        lean_ctor_set(v___x_1040_, 0, v___x_1049_);
                        v___x_1052_ = v___x_1040_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1049_);
                        lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1050_);
                        v___x_1052_ = v_reuseFailAlloc_1059_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1053_ = l_Lean_Syntax_ofRange(v___x_1052_, v___x_1044_);
                v___x_1054_ = 0;
                v___x_1055_ = l_Lean_mkIdentFrom(v___x_1053_, v_a_1034_, v___x_1054_);
                lean_dec(v___x_1053_);
                v___x_1056_ = lean_array_push(v_c_1036_, v___x_1055_);
                v___x_1057_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1057_, 0, v___x_1056_);
                v___x_1058_ = lean_apply_2(v_toPure_1033_, lean_box(0), v___x_1057_);
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(
    mut v_fm_1061_: *mut LeanObject,
    mut v_pos_1062_: *mut LeanObject,
    mut v_toPure_1063_: *mut LeanObject,
    mut v_a_1064_: *mut LeanObject,
    mut v_b_1065_: *mut LeanObject,
    mut v_c_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1067_: *mut LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(
        v_fm_1061_,
        v_pos_1062_,
        v_toPure_1063_,
        v_a_1064_,
        v_b_1065_,
        v_c_1066_,
    );
    lean_dec(v_pos_1062_);
    lean_dec_ref(v_fm_1061_);
    return v_res_1067_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(
    mut v_pos_1070_: *mut LeanObject,
    mut v_toPure_1071_: *mut LeanObject,
    mut v_inst_1072_: *mut LeanObject,
    mut v_drs_1073_: *mut LeanObject,
    mut v_toBind_1074_: *mut LeanObject,
    mut v___f_1075_: *mut LeanObject,
    mut v___f_1076_: *mut LeanObject,
    mut v_fm_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nms_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___f_1078_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_1078_, 0, v_fm_1077_);
    lean_closure_set(v___f_1078_, 1, v_pos_1070_);
    lean_closure_set(v___f_1078_, 2, v_toPure_1071_);
    v_nms_1079_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0;
    v___x_1080_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_1072_,
        v___f_1078_,
        v_nms_1079_,
        v_drs_1073_,
    );
    lean_inc(v_toBind_1074_);
    v___x_1081_ = lean_apply_4(
        v_toBind_1074_,
        lean_box(0),
        lean_box(0),
        v___x_1080_,
        v___f_1075_,
    );
    v___x_1082_ = lean_apply_4(
        v_toBind_1074_,
        lean_box(0),
        lean_box(0),
        v___x_1081_,
        v___f_1076_,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4(
    mut v___x_1083_: *mut LeanObject,
    mut v_pos_1084_: *mut LeanObject,
    mut v_toPure_1085_: *mut LeanObject,
    mut v_inst_1086_: *mut LeanObject,
    mut v_toBind_1087_: *mut LeanObject,
    mut v___f_1088_: *mut LeanObject,
    mut v___f_1089_: *mut LeanObject,
    mut v_inst_1090_: *mut LeanObject,
    mut v_____do__lift_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drs_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    v___x_1092_ = l_Lean_declRangeExt;
    v___x_1093_ = lean_box(1);
    v___x_1094_ = lean_box(0);
    v_drs_1095_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1083_,
        v___x_1092_,
        v_____do__lift_1091_,
        v___x_1093_,
        v___x_1094_,
    );
    lean_inc(v_toBind_1087_);
    v___f_1096_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1096_, 0, v_pos_1084_);
    lean_closure_set(v___f_1096_, 1, v_toPure_1085_);
    lean_closure_set(v___f_1096_, 2, v_inst_1086_);
    lean_closure_set(v___f_1096_, 3, v_drs_1095_);
    lean_closure_set(v___f_1096_, 4, v_toBind_1087_);
    lean_closure_set(v___f_1096_, 5, v___f_1088_);
    lean_closure_set(v___f_1096_, 6, v___f_1089_);
    v___x_1097_ = lean_apply_4(
        v_toBind_1087_,
        lean_box(0),
        lean_box(0),
        v_inst_1090_,
        v___f_1096_,
    );
    return v___x_1097_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(
    mut v_inst_1098_: *mut LeanObject,
    mut v_inst_1099_: *mut LeanObject,
    mut v_inst_1100_: *mut LeanObject,
    mut v_pos_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1102_ = lean_ctor_get(v_inst_1098_, 0);
    v_toBind_1103_ = lean_ctor_get(v_inst_1098_, 1);
    lean_inc_n(v_toBind_1103_, 2);
    v_getEnv_1104_ = lean_ctor_get(v_inst_1099_, 0);
    lean_inc(v_getEnv_1104_);
    lean_dec_ref(v_inst_1099_);
    v_toPure_1105_ = lean_ctor_get(v_toApplicative_1102_, 1);
    lean_inc_n(v_toPure_1105_, 3);
    v___x_1106_ = lean_box(1);
    v___f_1107_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1107_, 0, v_toPure_1105_);
    v___f_1108_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1108_, 0, v_toPure_1105_);
    v___f_1109_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1109_, 0, v___x_1106_);
    lean_closure_set(v___f_1109_, 1, v_pos_1101_);
    lean_closure_set(v___f_1109_, 2, v_toPure_1105_);
    lean_closure_set(v___f_1109_, 3, v_inst_1098_);
    lean_closure_set(v___f_1109_, 4, v_toBind_1103_);
    lean_closure_set(v___f_1109_, 5, v___f_1107_);
    lean_closure_set(v___f_1109_, 6, v___f_1108_);
    lean_closure_set(v___f_1109_, 7, v_inst_1100_);
    v___x_1110_ = lean_apply_4(
        v_toBind_1103_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1104_,
        v___f_1109_,
    );
    return v___x_1110_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom(
    mut v_m_1111_: *mut LeanObject,
    mut v_inst_1112_: *mut LeanObject,
    mut v_inst_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_pos_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    v___x_1116_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(
        v_inst_1112_,
        v_inst_1113_,
        v_inst_1114_,
        v_pos_1115_,
    );
    return v___x_1116_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(
    mut v___x_1117_: u8,
    mut v_currNamespace_1118_: *mut LeanObject,
    mut v_toPure_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_x_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    let mut v___y_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1123_ = l_Lean_TSyntax_getId(v_a_1120_);
                v___x_1124_ = 0;
                v___x_1133_ = l_Lean_Syntax_getRange_x3f(v_a_1120_, v___x_1124_);
                if lean_obj_tag(v___x_1133_) == 0 {
                    v___x_1134_ = l_Lean_Syntax_instInhabitedRange_default;
                    v___y_1126_ = v___x_1134_;
                    state = 1;
                    continue;
                } else {
                    v_val_1135_ = lean_ctor_get(v___x_1133_, 0);
                    lean_inc(v_val_1135_);
                    lean_dec_ref_known(v___x_1133_, 1);
                    v___y_1126_ = v_val_1135_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1127_ = l_Lean_Syntax_ofRange(v___y_1126_, v___x_1117_);
                v___x_1128_ = l_Lean_Name_append(v_currNamespace_1118_, v___x_1123_);
                v___x_1129_ = l_Lean_mkIdentFrom(v___x_1127_, v___x_1128_, v___x_1124_);
                lean_dec(v___x_1127_);
                v___x_1130_ = lean_array_push(v___y_1122_, v___x_1129_);
                v___x_1131_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                v___x_1132_ = lean_apply_2(v_toPure_1119_, lean_box(0), v___x_1131_);
                return v___x_1132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed(
    mut v___x_1136_: *mut LeanObject,
    mut v_currNamespace_1137_: *mut LeanObject,
    mut v_toPure_1138_: *mut LeanObject,
    mut v_a_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301__boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut LeanObject = core::ptr::null_mut();
    v___x_301__boxed_1142_ = (lean_unbox(v___x_1136_) as u8);
    v_res_1143_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(
        v___x_301__boxed_1142_,
        v_currNamespace_1137_,
        v_toPure_1138_,
        v_a_1139_,
        v_x_1140_,
        v___y_1141_,
    );
    lean_dec(v_a_1139_);
    return v_res_1143_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(
    mut v___x_1144_: u8,
    mut v_toPure_1145_: *mut LeanObject,
    mut v_ids_1146_: *mut LeanObject,
    mut v_inst_1147_: *mut LeanObject,
    mut v_aliases_1148_: *mut LeanObject,
    mut v_toBind_1149_: *mut LeanObject,
    mut v___f_1150_: *mut LeanObject,
    mut v_currNamespace_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1154_: usize = 0;
    let mut v___x_1155_: usize = 0;
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1152_ = lean_box((v___x_1144_) as usize);
    v___f_1153_ = lean_alloc_closure(
        l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_1153_, 0, v___x_1152_);
    lean_closure_set(v___f_1153_, 1, v_currNamespace_1151_);
    lean_closure_set(v___f_1153_, 2, v_toPure_1145_);
    v_sz_1154_ = lean_array_size(v_ids_1146_);
    v___x_1155_ = 0usize;
    v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_1147_,
        v_ids_1146_,
        v___f_1153_,
        v_sz_1154_,
        v___x_1155_,
        v_aliases_1148_,
    );
    v___x_1157_ = lean_apply_4(
        v_toBind_1149_,
        lean_box(0),
        lean_box(0),
        v___x_1156_,
        v___f_1150_,
    );
    return v___x_1157_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed(
    mut v___x_1158_: *mut LeanObject,
    mut v_toPure_1159_: *mut LeanObject,
    mut v_ids_1160_: *mut LeanObject,
    mut v_inst_1161_: *mut LeanObject,
    mut v_aliases_1162_: *mut LeanObject,
    mut v_toBind_1163_: *mut LeanObject,
    mut v___f_1164_: *mut LeanObject,
    mut v_currNamespace_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_336__boxed_1166_: u8 = 0;
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_336__boxed_1166_ = (lean_unbox(v___x_1158_) as u8);
    v_res_1167_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(
        v___x_336__boxed_1166_,
        v_toPure_1159_,
        v_ids_1160_,
        v_inst_1161_,
        v_aliases_1162_,
        v_toBind_1163_,
        v___f_1164_,
        v_currNamespace_1165_,
    );
    return v_res_1167_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(
    mut v_inst_1176_: *mut LeanObject,
    mut v_inst_1177_: *mut LeanObject,
    mut v_stx_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aliases_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: u8 = 0;
    v_toApplicative_1179_ = lean_ctor_get(v_inst_1176_, 0);
    v_toBind_1180_ = lean_ctor_get(v_inst_1176_, 1);
    lean_inc(v_toBind_1180_);
    v_toPure_1181_ = lean_ctor_get(v_toApplicative_1179_, 1);
    lean_inc(v_toPure_1181_);
    v_aliases_1182_ =
        l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0;
    v___x_1183_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3;
    lean_inc(v_stx_1178_);
    v___x_1184_ = l_Lean_Syntax_isOfKind(v_stx_1178_, v___x_1183_);
    if v___x_1184_ == 0 {
        let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_1180_);
        lean_dec(v_stx_1178_);
        lean_dec_ref(v_inst_1177_);
        lean_dec_ref(v_inst_1176_);
        v___x_1185_ = lean_apply_2(v_toPure_1181_, lean_box(0), v_aliases_1182_);
        return v___x_1185_;
    } else {
        let mut v_getCurrNamespace_1186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ids_1190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
        v_getCurrNamespace_1186_ = lean_ctor_get(v_inst_1177_, 0);
        lean_inc(v_getCurrNamespace_1186_);
        lean_dec_ref(v_inst_1177_);
        lean_inc(v_toPure_1181_);
        v___f_1187_ = lean_alloc_closure(
            l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_1187_, 0, v_toPure_1181_);
        v___x_1188_ = lean_unsigned_to_nat(3);
        v___x_1189_ = l_Lean_Syntax_getArg(v_stx_1178_, v___x_1188_);
        lean_dec(v_stx_1178_);
        v_ids_1190_ = l_Lean_Syntax_getArgs(v___x_1189_);
        lean_dec(v___x_1189_);
        v___x_1191_ = lean_box((v___x_1184_) as usize);
        lean_inc(v_toBind_1180_);
        v___f_1192_ = lean_alloc_closure(
            l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_1192_, 0, v___x_1191_);
        lean_closure_set(v___f_1192_, 1, v_toPure_1181_);
        lean_closure_set(v___f_1192_, 2, v_ids_1190_);
        lean_closure_set(v___f_1192_, 3, v_inst_1176_);
        lean_closure_set(v___f_1192_, 4, v_aliases_1182_);
        lean_closure_set(v___f_1192_, 5, v_toBind_1180_);
        lean_closure_set(v___f_1192_, 6, v___f_1187_);
        v___x_1193_ = lean_apply_4(
            v_toBind_1180_,
            lean_box(0),
            lean_box(0),
            v_getCurrNamespace_1186_,
            v___f_1192_,
        );
        return v___x_1193_;
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(
    mut v_m_1194_: *mut LeanObject,
    mut v_inst_1195_: *mut LeanObject,
    mut v_inst_1196_: *mut LeanObject,
    mut v_stx_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(
        v_inst_1195_,
        v_inst_1196_,
        v_stx_1197_,
    );
    return v___x_1198_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(
    mut v_x_1199_: *mut LeanObject,
) -> u8 {
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    v___x_1200_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3;
    v___x_1201_ = l_Lean_Syntax_isOfKind(v_x_1199_, v___x_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(
    mut v_x_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1203_: u8 = 0;
    let mut v_r_1204_: *mut LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(v_x_1202_);
    v_r_1204_ = lean_box((v_res_1203_) as usize);
    return v_r_1204_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(
    mut v___x_1205_: *mut LeanObject,
    mut v_pos_1206_: *mut LeanObject,
    mut v_init_1207_: *mut LeanObject,
    mut v_x_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1226_: u8 = 0;
    let mut v_pos_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: u8 = 0;
    let mut v_a_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_unused_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1208_) == 0 {
                    v_k_1214_ = lean_ctor_get(v_x_1208_, 1);
                    lean_inc(v_k_1214_);
                    v_v_1215_ = lean_ctor_get(v_x_1208_, 2);
                    lean_inc(v_v_1215_);
                    v_l_1216_ = lean_ctor_get(v_x_1208_, 3);
                    lean_inc(v_l_1216_);
                    v_r_1217_ = lean_ctor_get(v_x_1208_, 4);
                    lean_inc(v_r_1217_);
                    lean_dec_ref_known(v_x_1208_, 5);
                    v___x_1218_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1205_, v_pos_1206_, v_init_1207_, v_l_1216_);
                    v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
                    lean_inc(v_a_1219_);
                    if lean_obj_tag(v_a_1219_) == 0 {
                        lean_dec_ref(v___x_1218_);
                        lean_dec(v_r_1217_);
                        lean_dec(v_v_1215_);
                        lean_dec(v_k_1214_);
                        v_a_1220_ = lean_ctor_get(v_a_1219_, 0);
                        lean_inc(v_a_1220_);
                        lean_dec_ref_known(v_a_1219_, 1);
                        v_d_1211_ = v_a_1220_;
                        state = 1;
                        continue;
                    } else {
                        v_range_1221_ = lean_ctor_get(v_v_1215_, 0);
                        lean_inc_ref(v_range_1221_);
                        v_a_1222_ = lean_ctor_get(v_a_1219_, 0);
                        lean_inc(v_a_1222_);
                        lean_dec_ref_known(v_a_1219_, 1);
                        v_selectionRange_1223_ = lean_ctor_get(v_v_1215_, 1);
                        v_isSharedCheck_1246_ = (!lean_is_exclusive(v_v_1215_)) as u8;
                        if v_isSharedCheck_1246_ == 0 {
                            v_unused_1247_ = lean_ctor_get(v_v_1215_, 0);
                            lean_dec(v_unused_1247_);
                            v___x_1225_ = v_v_1215_;
                            v_isShared_1226_ = v_isSharedCheck_1246_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_selectionRange_1223_);
                            lean_dec(v_v_1215_);
                            v___x_1225_ = lean_box(0);
                            v_isShared_1226_ = v_isSharedCheck_1246_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1248_, 0, v_init_1207_);
                    v___x_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1249_, 0, v___x_1248_);
                    return v___x_1249_;
                }
            }
            1 => {
                v___x_1212_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1212_, 0, v_d_1211_);
                v___x_1213_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1213_, 0, v___x_1212_);
                return v___x_1213_;
            }
            2 => {
                v_pos_1227_ = lean_ctor_get(v_range_1221_, 0);
                lean_inc_ref(v_pos_1227_);
                lean_dec_ref(v_range_1221_);
                v___x_1228_ = l_Lean_FileMap_ofPosition(v___x_1205_, v_pos_1227_);
                v___x_1229_ = lean_nat_dec_le(v_pos_1206_, v___x_1228_);
                lean_dec(v___x_1228_);
                if v___x_1229_ == 0 {
                    lean_del_object(v___x_1225_);
                    lean_dec_ref(v_selectionRange_1223_);
                    lean_dec(v_a_1222_);
                    lean_dec(v_k_1214_);
                    v_a_1230_ = lean_ctor_get(v___x_1218_, 0);
                    lean_inc(v_a_1230_);
                    lean_dec_ref(v___x_1218_);
                    if lean_obj_tag(v_a_1230_) == 0 {
                        lean_dec(v_r_1217_);
                        v_a_1231_ = lean_ctor_get(v_a_1230_, 0);
                        lean_inc(v_a_1231_);
                        lean_dec_ref_known(v_a_1230_, 1);
                        v_d_1211_ = v_a_1231_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1232_ = lean_ctor_get(v_a_1230_, 0);
                        lean_inc(v_a_1232_);
                        lean_dec_ref_known(v_a_1230_, 1);
                        v_init_1207_ = v_a_1232_;
                        v_x_1208_ = v_r_1217_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1218_);
                    v_pos_1234_ = lean_ctor_get(v_selectionRange_1223_, 0);
                    lean_inc_ref(v_pos_1234_);
                    v_endPos_1235_ = lean_ctor_get(v_selectionRange_1223_, 2);
                    lean_inc_ref(v_endPos_1235_);
                    lean_dec_ref(v_selectionRange_1223_);
                    v___x_1236_ = l_Lean_FileMap_ofPosition(v___x_1205_, v_pos_1234_);
                    v___x_1237_ = l_Lean_FileMap_ofPosition(v___x_1205_, v_endPos_1235_);
                    if v_isShared_1226_ == 0 {
                        lean_ctor_set(v___x_1225_, 1, v___x_1237_);
                        lean_ctor_set(v___x_1225_, 0, v___x_1236_);
                        v___x_1239_ = v___x_1225_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1236_);
                        lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1237_);
                        v___x_1239_ = v_reuseFailAlloc_1245_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1240_ = l_Lean_Syntax_ofRange(v___x_1239_, v___x_1229_);
                v___x_1241_ = 0;
                v___x_1242_ = l_Lean_mkIdentFrom(v___x_1240_, v_k_1214_, v___x_1241_);
                lean_dec(v___x_1240_);
                v___x_1243_ = lean_array_push(v_a_1222_, v___x_1242_);
                v_init_1207_ = v___x_1243_;
                v_x_1208_ = v_r_1217_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(
    mut v___x_1250_: *mut LeanObject,
    mut v_pos_1251_: *mut LeanObject,
    mut v_init_1252_: *mut LeanObject,
    mut v_x_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1255_: *mut LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1250_, v_pos_1251_, v_init_1252_, v_x_1253_);
    lean_dec(v_pos_1251_);
    lean_dec_ref(v___x_1250_);
    return v_res_1255_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(
    mut v_pos_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_drs_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nms_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1273_: u8 = 0;
    let mut v_a_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1260_ = lean_st_ref_get(v___y_1258_);
                v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
                lean_inc_ref(v_env_1261_);
                lean_dec(v___x_1260_);
                v_fileMap_1262_ = lean_ctor_get(v___y_1257_, 1);
                v___x_1263_ = lean_box(1);
                v___x_1264_ = l_Lean_declRangeExt;
                v___x_1265_ = lean_box(1);
                v___x_1266_ = lean_box(0);
                v_drs_1267_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_1263_,
                    v___x_1264_,
                    v_env_1261_,
                    v___x_1265_,
                    v___x_1266_,
                );
                v_nms_1268_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0;
                v___x_1269_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_1262_, v_pos_1256_, v_nms_1268_, v_drs_1267_);
                v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
                v_isSharedCheck_1278_ = (!lean_is_exclusive(v___x_1269_)) as u8;
                if v_isSharedCheck_1278_ == 0 {
                    v___x_1272_ = v___x_1269_;
                    v_isShared_1273_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1270_);
                    lean_dec(v___x_1269_);
                    v___x_1272_ = lean_box(0);
                    v_isShared_1273_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_a_1274_ = lean_ctor_get(v_a_1270_, 0);
                lean_inc(v_a_1274_);
                lean_dec(v_a_1270_);
                if v_isShared_1273_ == 0 {
                    lean_ctor_set(v___x_1272_, 0, v_a_1274_);
                    v___x_1276_ = v___x_1272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1274_);
                    v___x_1276_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(
    mut v_pos_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v_pos_1279_, v___y_1280_, v___y_1281_);
    lean_dec(v___y_1281_);
    lean_dec_ref(v___y_1280_);
    lean_dec(v_pos_1279_);
    return v_res_1283_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(
    mut v_x_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1284_) == 0 {
                    v___x_1285_ = lean_box(0);
                    return v___x_1285_;
                } else {
                    v_head_1286_ = lean_ctor_get(v_x_1284_, 0);
                    v_tail_1287_ = lean_ctor_get(v_x_1284_, 1);
                    v_fst_1288_ = lean_ctor_get(v_head_1286_, 0);
                    v_snd_1289_ = lean_ctor_get(v_head_1286_, 1);
                    v___x_1290_ = lean_name_eq(v_fst_1288_, v_snd_1289_);
                    if v___x_1290_ == 0 {
                        v_x_1284_ = v_tail_1287_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_1286_);
                        v___x_1292_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1292_, 0, v_head_1286_);
                        return v___x_1292_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(
    mut v_x_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_res_1294_ =
        l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(
            v_x_1293_,
        );
    lean_dec(v_x_1293_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0(
    mut v___y_1296_: u8,
    mut v_suppressElabErrors_1297_: u8,
    mut v_x_1298_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1298_) == 1 {
        let mut v_pre_1299_: *mut LeanObject = core::ptr::null_mut();
        v_pre_1299_ = lean_ctor_get(v_x_1298_, 0);
        if lean_obj_tag(v_pre_1299_) == 0 {
            let mut v_str_1300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1302_: u8 = 0;
            v_str_1300_ = lean_ctor_get(v_x_1298_, 1);
            v___x_1301_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0;
            v___x_1302_ = lean_string_dec_eq(v_str_1300_, v___x_1301_);
            if v___x_1302_ == 0 {
                return v___y_1296_;
            } else {
                return v_suppressElabErrors_1297_;
            }
        } else {
            return v___y_1296_;
        }
    } else {
        return v___y_1296_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___boxed(
    mut v___y_1303_: *mut LeanObject,
    mut v_suppressElabErrors_1304_: *mut LeanObject,
    mut v_x_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6963__boxed_1306_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1307_: u8 = 0;
    let mut v_res_1308_: u8 = 0;
    let mut v_r_1309_: *mut LeanObject = core::ptr::null_mut();
    v___y_6963__boxed_1306_ = (lean_unbox(v___y_1303_) as u8);
    v_suppressElabErrors_boxed_1307_ = (lean_unbox(v_suppressElabErrors_1304_) as u8);
    v_res_1308_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0(v___y_6963__boxed_1306_, v_suppressElabErrors_boxed_1307_, v_x_1305_);
    lean_dec(v_x_1305_);
    v_r_1309_ = lean_box((v_res_1308_) as usize);
    return v_r_1309_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(
    mut v_opts_1310_: *mut LeanObject,
    mut v_opt_1311_: *mut LeanObject,
) -> u8 {
    let mut v_name_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v_name_1312_ = lean_ctor_get(v_opt_1311_, 0);
    v_defValue_1313_ = lean_ctor_get(v_opt_1311_, 1);
    v_map_1314_ = lean_ctor_get(v_opts_1310_, 0);
    v___x_1315_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1314_,
            v_name_1312_,
        );
    if lean_obj_tag(v___x_1315_) == 0 {
        let mut v___x_1316_: u8 = 0;
        v___x_1316_ = (lean_unbox(v_defValue_1313_) as u8);
        return v___x_1316_;
    } else {
        let mut v_val_1317_: *mut LeanObject = core::ptr::null_mut();
        v_val_1317_ = lean_ctor_get(v___x_1315_, 0);
        lean_inc(v_val_1317_);
        lean_dec_ref_known(v___x_1315_, 1);
        if lean_obj_tag(v_val_1317_) == 1 {
            let mut v_v_1318_: u8 = 0;
            v_v_1318_ = lean_ctor_get_uint8(v_val_1317_, 0 as u32);
            lean_dec_ref_known(v_val_1317_, 0);
            return v_v_1318_;
        } else {
            let mut v___x_1319_: u8 = 0;
            lean_dec(v_val_1317_);
            v___x_1319_ = (lean_unbox(v_defValue_1313_) as u8);
            return v___x_1319_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(
    mut v_opts_1320_: *mut LeanObject,
    mut v_opt_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: u8 = 0;
    let mut v_r_1323_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(v_opts_1320_, v_opt_1321_);
    lean_dec_ref(v_opt_1321_);
    lean_dec_ref(v_opts_1320_);
    v_r_1323_ = lean_box((v_res_1322_) as usize);
    return v_r_1323_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    v___x_1324_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1324_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0);
    v___x_1326_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1326_, 0, v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1);
    v___x_1328_ = lean_unsigned_to_nat(0);
    v___x_1329_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1329_, 0, v___x_1328_);
    lean_ctor_set(v___x_1329_, 1, v___x_1328_);
    lean_ctor_set(v___x_1329_, 2, v___x_1328_);
    lean_ctor_set(v___x_1329_, 3, v___x_1328_);
    lean_ctor_set(v___x_1329_, 4, v___x_1327_);
    lean_ctor_set(v___x_1329_, 5, v___x_1327_);
    lean_ctor_set(v___x_1329_, 6, v___x_1327_);
    lean_ctor_set(v___x_1329_, 7, v___x_1327_);
    lean_ctor_set(v___x_1329_, 8, v___x_1327_);
    lean_ctor_set(v___x_1329_, 9, v___x_1327_);
    return v___x_1329_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1330_ = lean_unsigned_to_nat(32);
    v___x_1331_ = lean_mk_empty_array_with_capacity(v___x_1330_);
    v___x_1332_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1332_, 0, v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v___x_1333_ = 5usize;
    v___x_1334_ = lean_unsigned_to_nat(0);
    v___x_1335_ = lean_unsigned_to_nat(32);
    v___x_1336_ = lean_mk_empty_array_with_capacity(v___x_1335_);
    v___x_1337_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3);
    v___x_1338_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1338_, 0, v___x_1337_);
    lean_ctor_set(v___x_1338_, 1, v___x_1336_);
    lean_ctor_set(v___x_1338_, 2, v___x_1334_);
    lean_ctor_set(v___x_1338_, 3, v___x_1334_);
    lean_ctor_set_usize(v___x_1338_, 4, v___x_1333_);
    return v___x_1338_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = lean_box(1);
    v___x_1340_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4);
    v___x_1341_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1);
    v___x_1342_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1342_, 0, v___x_1341_);
    lean_ctor_set(v___x_1342_, 1, v___x_1340_);
    lean_ctor_set(v___x_1342_, 2, v___x_1339_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(
    mut v_msgData_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v___x_1346_ = lean_st_ref_get(v___y_1344_);
    v_env_1347_ = lean_ctor_get(v___x_1346_, 0);
    lean_inc_ref(v_env_1347_);
    lean_dec(v___x_1346_);
    v___x_1348_ = lean_st_ref_get(v___y_1344_);
    v_scopes_1349_ = lean_ctor_get(v___x_1348_, 2);
    lean_inc(v_scopes_1349_);
    lean_dec(v___x_1348_);
    v___x_1350_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1351_ = l_List_head_x21___redArg(v___x_1350_, v_scopes_1349_);
    lean_dec(v_scopes_1349_);
    v_opts_1352_ = lean_ctor_get(v___x_1351_, 1);
    lean_inc_ref(v_opts_1352_);
    lean_dec(v___x_1351_);
    v___x_1353_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2);
    v___x_1354_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5);
    v___x_1355_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1355_, 0, v_env_1347_);
    lean_ctor_set(v___x_1355_, 1, v___x_1353_);
    lean_ctor_set(v___x_1355_, 2, v___x_1354_);
    lean_ctor_set(v___x_1355_, 3, v_opts_1352_);
    v___x_1356_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1356_, 0, v___x_1355_);
    lean_ctor_set(v___x_1356_, 1, v_msgData_1343_);
    v___x_1357_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1357_, 0, v___x_1356_);
    return v___x_1357_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___boxed(
    mut v_msgData_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v_msgData_1358_, v___y_1359_);
    lean_dec(v___y_1359_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(
    mut v_ref_1363_: *mut LeanObject,
    mut v_msgData_1364_: *mut LeanObject,
    mut v_severity_1365_: u8,
    mut v_isSilent_1366_: u8,
    mut v___y_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1371_: u8 = 0;
    let mut v___y_1372_: u8 = 0;
    let mut v___y_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_a_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1424_: u8 = 0;
    let mut v_a_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1432_: u8 = 0;
    let mut v___y_1434_: u8 = 0;
    let mut v___y_1435_: u8 = 0;
    let mut v___y_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1437_: u8 = 0;
    let mut v___y_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1441_: u8 = 0;
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v___y_1462_: u8 = 0;
    let mut v___y_1463_: u8 = 0;
    let mut v___y_1464_: u8 = 0;
    let mut v___y_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v___y_1472_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v___x_1487_: u8 = 0;
    let mut v___y_1489_: u8 = 0;
    let mut v___y_1490_: u8 = 0;
    let mut v___y_1491_: u8 = 0;
    let mut v___y_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1487_ = 2;
                v___x_1505_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1365_, v___x_1487_);
                if v___x_1505_ == 0 {
                    v___y_1493_ = v___x_1505_;
                    state = 18;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_1364_);
                    v___x_1506_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1364_);
                    v___y_1493_ = v___x_1506_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1379_ = l_Lean_Elab_Command_getScope___redArg(v___y_1378_);
                if lean_obj_tag(v___x_1379_) == 0 {
                    v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
                    lean_inc(v_a_1380_);
                    lean_dec_ref_known(v___x_1379_, 1);
                    v___x_1381_ = l_Lean_Elab_Command_getScope___redArg(v___y_1378_);
                    if lean_obj_tag(v___x_1381_) == 0 {
                        v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
                        v_isSharedCheck_1416_ = (!lean_is_exclusive(v___x_1381_)) as u8;
                        if v_isSharedCheck_1416_ == 0 {
                            v___x_1384_ = v___x_1381_;
                            v_isShared_1385_ = v_isSharedCheck_1416_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1382_);
                            lean_dec(v___x_1381_);
                            v___x_1384_ = lean_box(0);
                            v_isShared_1385_ = v_isSharedCheck_1416_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1380_);
                        lean_dec(v___y_1377_);
                        lean_dec_ref(v___y_1376_);
                        lean_dec_ref(v___y_1373_);
                        v_a_1417_ = lean_ctor_get(v___x_1381_, 0);
                        v_isSharedCheck_1424_ = (!lean_is_exclusive(v___x_1381_)) as u8;
                        if v_isSharedCheck_1424_ == 0 {
                            v___x_1419_ = v___x_1381_;
                            v_isShared_1420_ = v_isSharedCheck_1424_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1417_);
                            lean_dec(v___x_1381_);
                            v___x_1419_ = lean_box(0);
                            v_isShared_1420_ = v_isSharedCheck_1424_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1377_);
                    lean_dec_ref(v___y_1376_);
                    lean_dec_ref(v___y_1373_);
                    v_a_1425_ = lean_ctor_get(v___x_1379_, 0);
                    v_isSharedCheck_1432_ = (!lean_is_exclusive(v___x_1379_)) as u8;
                    if v_isSharedCheck_1432_ == 0 {
                        v___x_1427_ = v___x_1379_;
                        v_isShared_1428_ = v_isSharedCheck_1432_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1425_);
                        lean_dec(v___x_1379_);
                        v___x_1427_ = lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1432_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1386_ = lean_st_ref_take(v___y_1378_);
                v_currNamespace_1387_ = lean_ctor_get(v_a_1380_, 2);
                lean_inc(v_currNamespace_1387_);
                lean_dec(v_a_1380_);
                v_openDecls_1388_ = lean_ctor_get(v_a_1382_, 3);
                lean_inc(v_openDecls_1388_);
                lean_dec(v_a_1382_);
                v_env_1389_ = lean_ctor_get(v___x_1386_, 0);
                v_messages_1390_ = lean_ctor_get(v___x_1386_, 1);
                v_scopes_1391_ = lean_ctor_get(v___x_1386_, 2);
                v_usedQuotCtxts_1392_ = lean_ctor_get(v___x_1386_, 3);
                v_nextMacroScope_1393_ = lean_ctor_get(v___x_1386_, 4);
                v_maxRecDepth_1394_ = lean_ctor_get(v___x_1386_, 5);
                v_ngen_1395_ = lean_ctor_get(v___x_1386_, 6);
                v_auxDeclNGen_1396_ = lean_ctor_get(v___x_1386_, 7);
                v_infoState_1397_ = lean_ctor_get(v___x_1386_, 8);
                v_traceState_1398_ = lean_ctor_get(v___x_1386_, 9);
                v_snapshotTasks_1399_ = lean_ctor_get(v___x_1386_, 10);
                v_isSharedCheck_1415_ = (!lean_is_exclusive(v___x_1386_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1401_ = v___x_1386_;
                    v_isShared_1402_ = v_isSharedCheck_1415_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1399_);
                    lean_inc(v_traceState_1398_);
                    lean_inc(v_infoState_1397_);
                    lean_inc(v_auxDeclNGen_1396_);
                    lean_inc(v_ngen_1395_);
                    lean_inc(v_maxRecDepth_1394_);
                    lean_inc(v_nextMacroScope_1393_);
                    lean_inc(v_usedQuotCtxts_1392_);
                    lean_inc(v_scopes_1391_);
                    lean_inc(v_messages_1390_);
                    lean_inc(v_env_1389_);
                    lean_dec(v___x_1386_);
                    v___x_1401_ = lean_box(0);
                    v_isShared_1402_ = v_isSharedCheck_1415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1403_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1403_, 0, v_currNamespace_1387_);
                lean_ctor_set(v___x_1403_, 1, v_openDecls_1388_);
                v___x_1404_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1404_, 0, v___x_1403_);
                lean_ctor_set(v___x_1404_, 1, v___y_1376_);
                lean_inc_ref(v___y_1374_);
                lean_inc_ref(v___y_1375_);
                v___x_1405_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_1405_, 0, v___y_1375_);
                lean_ctor_set(v___x_1405_, 1, v___y_1373_);
                lean_ctor_set(v___x_1405_, 2, v___y_1377_);
                lean_ctor_set(v___x_1405_, 3, v___y_1374_);
                lean_ctor_set(v___x_1405_, 4, v___x_1404_);
                lean_ctor_set_uint8(
                    v___x_1405_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_1372_,
                );
                lean_ctor_set_uint8(
                    v___x_1405_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_1371_,
                );
                lean_ctor_set_uint8(
                    v___x_1405_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1366_,
                );
                v___x_1406_ = l_Lean_MessageLog_add(v___x_1405_, v_messages_1390_);
                if v_isShared_1402_ == 0 {
                    lean_ctor_set(v___x_1401_, 1, v___x_1406_);
                    v___x_1408_ = v___x_1401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_env_1389_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_scopes_1391_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_usedQuotCtxts_1392_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_nextMacroScope_1393_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 5, v_maxRecDepth_1394_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 6, v_ngen_1395_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 7, v_auxDeclNGen_1396_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 8, v_infoState_1397_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 9, v_traceState_1398_);
                    lean_ctor_set(v_reuseFailAlloc_1414_, 10, v_snapshotTasks_1399_);
                    v___x_1408_ = v_reuseFailAlloc_1414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1409_ = lean_st_ref_set(v___y_1378_, v___x_1408_);
                v___x_1410_ = lean_box(0);
                if v_isShared_1385_ == 0 {
                    lean_ctor_set(v___x_1384_, 0, v___x_1410_);
                    v___x_1412_ = v___x_1384_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1412_;
            }
            6 => {
                if v_isShared_1420_ == 0 {
                    v___x_1422_ = v___x_1419_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1422_;
            }
            8 => {
                if v_isShared_1428_ == 0 {
                    v___x_1430_ = v___x_1427_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1430_;
            }
            10 => {
                v_fileName_1439_ = lean_ctor_get(v___y_1367_, 0);
                v_fileMap_1440_ = lean_ctor_get(v___y_1367_, 1);
                v_suppressElabErrors_1441_ = lean_ctor_get_uint8(
                    v___y_1367_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_1442_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1364_,
                    );
                v___x_1443_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v___x_1442_, v___y_1368_);
                v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
                v_isSharedCheck_1460_ = (!lean_is_exclusive(v___x_1443_)) as u8;
                if v_isSharedCheck_1460_ == 0 {
                    v___x_1446_ = v___x_1443_;
                    v_isShared_1447_ = v_isSharedCheck_1460_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_1444_);
                    lean_dec(v___x_1443_);
                    v___x_1446_ = lean_box(0);
                    v_isShared_1447_ = v_isSharedCheck_1460_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_1440_, 2);
                v___x_1448_ = l_Lean_FileMap_toPosition(v_fileMap_1440_, v___y_1436_);
                lean_dec(v___y_1436_);
                v___x_1449_ = l_Lean_FileMap_toPosition(v_fileMap_1440_, v___y_1438_);
                lean_dec(v___y_1438_);
                v___x_1450_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1450_, 0, v___x_1449_);
                v___x_1451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0;
                if v_suppressElabErrors_1441_ == 0 {
                    lean_del_object(v___x_1446_);
                    v___y_1371_ = v___y_1435_;
                    v___y_1372_ = v___y_1437_;
                    v___y_1373_ = v___x_1448_;
                    v___y_1374_ = v___x_1451_;
                    v___y_1375_ = v_fileName_1439_;
                    v___y_1376_ = v_a_1444_;
                    v___y_1377_ = v___x_1450_;
                    v___y_1378_ = v___y_1368_;
                    state = 1;
                    continue;
                } else {
                    v___x_1452_ = lean_box((v___y_1434_) as usize);
                    v___x_1453_ = lean_box((v_suppressElabErrors_1441_) as usize);
                    v___f_1454_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_1454_, 0, v___x_1452_);
                    lean_closure_set(v___f_1454_, 1, v___x_1453_);
                    lean_inc(v_a_1444_);
                    v___x_1455_ = l_Lean_MessageData_hasTag(v___f_1454_, v_a_1444_);
                    if v___x_1455_ == 0 {
                        lean_dec_ref_known(v___x_1450_, 1);
                        lean_dec_ref(v___x_1448_);
                        lean_dec(v_a_1444_);
                        v___x_1456_ = lean_box(0);
                        if v_isShared_1447_ == 0 {
                            lean_ctor_set(v___x_1446_, 0, v___x_1456_);
                            v___x_1458_ = v___x_1446_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
                            v___x_1458_ = v_reuseFailAlloc_1459_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1446_);
                        v___y_1371_ = v___y_1435_;
                        v___y_1372_ = v___y_1437_;
                        v___y_1373_ = v___x_1448_;
                        v___y_1374_ = v___x_1451_;
                        v___y_1375_ = v_fileName_1439_;
                        v___y_1376_ = v_a_1444_;
                        v___y_1377_ = v___x_1450_;
                        v___y_1378_ = v___y_1368_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1458_;
            }
            13 => {
                v___x_1467_ = l_Lean_Syntax_getTailPos_x3f(v___y_1465_, v___y_1464_);
                lean_dec(v___y_1465_);
                if lean_obj_tag(v___x_1467_) == 0 {
                    lean_inc(v___y_1466_);
                    v___y_1434_ = v___y_1462_;
                    v___y_1435_ = v___y_1463_;
                    v___y_1436_ = v___y_1466_;
                    v___y_1437_ = v___y_1464_;
                    v___y_1438_ = v___y_1466_;
                    state = 10;
                    continue;
                } else {
                    v_val_1468_ = lean_ctor_get(v___x_1467_, 0);
                    lean_inc(v_val_1468_);
                    lean_dec_ref_known(v___x_1467_, 1);
                    v___y_1434_ = v___y_1462_;
                    v___y_1435_ = v___y_1463_;
                    v___y_1436_ = v___y_1466_;
                    v___y_1437_ = v___y_1464_;
                    v___y_1438_ = v_val_1468_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1473_ = l_Lean_Elab_Command_getRef___redArg(v___y_1367_);
                if lean_obj_tag(v___x_1473_) == 0 {
                    v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
                    lean_inc(v_a_1474_);
                    lean_dec_ref_known(v___x_1473_, 1);
                    v_ref_1475_ = l_Lean_replaceRef(v_ref_1363_, v_a_1474_);
                    lean_dec(v_a_1474_);
                    v___x_1476_ = l_Lean_Syntax_getPos_x3f(v_ref_1475_, v___y_1471_);
                    if lean_obj_tag(v___x_1476_) == 0 {
                        v___x_1477_ = lean_unsigned_to_nat(0);
                        v___y_1462_ = v___y_1470_;
                        v___y_1463_ = v___y_1472_;
                        v___y_1464_ = v___y_1471_;
                        v___y_1465_ = v_ref_1475_;
                        v___y_1466_ = v___x_1477_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1478_ = lean_ctor_get(v___x_1476_, 0);
                        lean_inc(v_val_1478_);
                        lean_dec_ref_known(v___x_1476_, 1);
                        v___y_1462_ = v___y_1470_;
                        v___y_1463_ = v___y_1472_;
                        v___y_1464_ = v___y_1471_;
                        v___y_1465_ = v_ref_1475_;
                        v___y_1466_ = v_val_1478_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1364_);
                    v_a_1479_ = lean_ctor_get(v___x_1473_, 0);
                    v_isSharedCheck_1486_ = (!lean_is_exclusive(v___x_1473_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1481_ = v___x_1473_;
                        v_isShared_1482_ = v_isSharedCheck_1486_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1479_);
                        lean_dec(v___x_1473_);
                        v___x_1481_ = lean_box(0);
                        v_isShared_1482_ = v_isSharedCheck_1486_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1482_ == 0 {
                    v___x_1484_ = v___x_1481_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
                    v___x_1484_ = v_reuseFailAlloc_1485_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1484_;
            }
            17 => {
                if v___y_1491_ == 0 {
                    v___y_1470_ = v___y_1489_;
                    v___y_1471_ = v___y_1490_;
                    v___y_1472_ = v_severity_1365_;
                    state = 14;
                    continue;
                } else {
                    v___y_1470_ = v___y_1489_;
                    v___y_1471_ = v___y_1490_;
                    v___y_1472_ = v___x_1487_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1493_ == 0 {
                    v___x_1494_ = lean_st_ref_get(v___y_1368_);
                    v_scopes_1495_ = lean_ctor_get(v___x_1494_, 2);
                    lean_inc(v_scopes_1495_);
                    lean_dec(v___x_1494_);
                    v___x_1496_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1497_ = l_List_head_x21___redArg(v___x_1496_, v_scopes_1495_);
                    lean_dec(v_scopes_1495_);
                    v_opts_1498_ = lean_ctor_get(v___x_1497_, 1);
                    lean_inc_ref(v_opts_1498_);
                    lean_dec(v___x_1497_);
                    v___x_1499_ = 1;
                    v___x_1500_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1365_, v___x_1499_);
                    if v___x_1500_ == 0 {
                        lean_dec_ref(v_opts_1498_);
                        v___y_1489_ = v___y_1493_;
                        v___y_1490_ = v___y_1493_;
                        v___y_1491_ = v___x_1500_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1501_ = l_Lean_warningAsError;
                        v___x_1502_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(v_opts_1498_, v___x_1501_);
                        lean_dec_ref(v_opts_1498_);
                        v___y_1489_ = v___y_1493_;
                        v___y_1490_ = v___y_1493_;
                        v___y_1491_ = v___x_1502_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1364_);
                    v___x_1503_ = lean_box(0);
                    v___x_1504_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1504_, 0, v___x_1503_);
                    return v___x_1504_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___boxed(
    mut v_ref_1507_: *mut LeanObject,
    mut v_msgData_1508_: *mut LeanObject,
    mut v_severity_1509_: *mut LeanObject,
    mut v_isSilent_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1514_: u8 = 0;
    let mut v_isSilent_boxed_1515_: u8 = 0;
    let mut v_res_1516_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1514_ = (lean_unbox(v_severity_1509_) as u8);
    v_isSilent_boxed_1515_ = (lean_unbox(v_isSilent_1510_) as u8);
    v_res_1516_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(v_ref_1507_, v_msgData_1508_, v_severity_boxed_1514_, v_isSilent_boxed_1515_, v___y_1511_, v___y_1512_);
    lean_dec(v___y_1512_);
    lean_dec_ref(v___y_1511_);
    lean_dec(v_ref_1507_);
    return v_res_1516_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(
    mut v_ref_1517_: *mut LeanObject,
    mut v_msgData_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
    mut v___y_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1522_ = 1;
    v___x_1523_ = 0;
    v___x_1524_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(v_ref_1517_, v_msgData_1518_, v___x_1522_, v___x_1523_, v___y_1519_, v___y_1520_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6___boxed(
    mut v_ref_1525_: *mut LeanObject,
    mut v_msgData_1526_: *mut LeanObject,
    mut v___y_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(v_ref_1525_, v_msgData_1526_, v___y_1527_, v___y_1528_);
    lean_dec(v___y_1528_);
    lean_dec_ref(v___y_1527_);
    lean_dec(v_ref_1525_);
    return v_res_1530_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0;
    v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
    return v___x_1533_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v___x_1535_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2;
    v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(
    mut v_linterOption_1537_: *mut LeanObject,
    mut v_stx_1538_: *mut LeanObject,
    mut v_msg_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_unused_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1543_ = lean_ctor_get(v_linterOption_1537_, 0);
                v_isSharedCheck_1560_ = (!lean_is_exclusive(v_linterOption_1537_)) as u8;
                if v_isSharedCheck_1560_ == 0 {
                    v_unused_1561_ = lean_ctor_get(v_linterOption_1537_, 1);
                    lean_dec(v_unused_1561_);
                    v___x_1545_ = v_linterOption_1537_;
                    v_isShared_1546_ = v_isSharedCheck_1560_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1543_);
                    lean_dec(v_linterOption_1537_);
                    v___x_1545_ = lean_box(0);
                    v_isShared_1546_ = v_isSharedCheck_1560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1547_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1);
                lean_inc(v_name_1543_);
                v___x_1548_ = l_Lean_MessageData_ofName(v_name_1543_);
                if v_isShared_1546_ == 0 {
                    lean_ctor_set_tag(v___x_1545_, 7);
                    lean_ctor_set(v___x_1545_, 1, v___x_1548_);
                    lean_ctor_set(v___x_1545_, 0, v___x_1547_);
                    v___x_1550_ = v___x_1545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1548_);
                    v___x_1550_ = v_reuseFailAlloc_1559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1551_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3);
                v___x_1552_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1552_, 0, v___x_1550_);
                lean_ctor_set(v___x_1552_, 1, v___x_1551_);
                v_disable_1553_ = l_Lean_MessageData_note(v___x_1552_);
                v___x_1554_ = l_Lean_Linter_linterMessageTag;
                v___x_1555_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1555_, 0, v_msg_1539_);
                lean_ctor_set(v___x_1555_, 1, v_disable_1553_);
                v___x_1556_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1556_, 0, v___x_1554_);
                lean_ctor_set(v___x_1556_, 1, v___x_1555_);
                v___x_1557_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1557_, 0, v_name_1543_);
                lean_ctor_set(v___x_1557_, 1, v___x_1556_);
                v___x_1558_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(v_stx_1538_, v___x_1557_, v___y_1540_, v___y_1541_);
                return v___x_1558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(
    mut v_linterOption_1562_: *mut LeanObject,
    mut v_stx_1563_: *mut LeanObject,
    mut v_msg_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1568_: *mut LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_linterOption_1562_, v_stx_1563_, v_msg_1564_, v___y_1565_, v___y_1566_);
    lean_dec(v___y_1566_);
    lean_dec_ref(v___y_1565_);
    lean_dec(v_stx_1563_);
    return v_res_1568_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(
    mut v_o_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = lean_st_ref_get(v___y_1570_);
    v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
    lean_inc_ref(v_env_1573_);
    lean_dec(v___x_1572_);
    v___x_1574_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_1575_ = lean_ctor_get(v___x_1574_, 0);
    v_asyncMode_1576_ = lean_ctor_get(v_toEnvExtension_1575_, 2);
    v___x_1577_ = lean_box(1);
    v___x_1578_ = lean_box(0);
    v_linterSets_1579_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1577_,
        v___x_1574_,
        v_env_1573_,
        v_asyncMode_1576_,
        v___x_1578_,
    );
    v___x_1580_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1580_, 0, v_o_1569_);
    lean_ctor_set(v___x_1580_, 1, v_linterSets_1579_);
    v___x_1581_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1581_, 0, v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(
    mut v_o_1582_: *mut LeanObject,
    mut v___y_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1585_: *mut LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_1582_, v___y_1583_);
    lean_dec(v___y_1583_);
    return v_res_1585_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = lean_st_ref_get(v___y_1587_);
    v_scopes_1590_ = lean_ctor_get(v___x_1589_, 2);
    lean_inc(v_scopes_1590_);
    lean_dec(v___x_1589_);
    v___x_1591_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1592_ = l_List_head_x21___redArg(v___x_1591_, v_scopes_1590_);
    lean_dec(v_scopes_1590_);
    v_opts_1593_ = lean_ctor_get(v___x_1592_, 1);
    lean_inc_ref(v_opts_1593_);
    lean_dec(v___x_1592_);
    v___x_1594_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_opts_1593_, v___y_1587_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_1595_, v___y_1596_);
    lean_dec(v___y_1596_);
    lean_dec_ref(v___y_1595_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(
    mut v_linterOption_1599_: *mut LeanObject,
    mut v_stx_1600_: *mut LeanObject,
    mut v_msg_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1605_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_1602_, v___y_1603_);
                v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
                v_isSharedCheck_1616_ = (!lean_is_exclusive(v___x_1605_)) as u8;
                if v_isSharedCheck_1616_ == 0 {
                    v___x_1608_ = v___x_1605_;
                    v_isShared_1609_ = v_isSharedCheck_1616_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1606_);
                    lean_dec(v___x_1605_);
                    v___x_1608_ = lean_box(0);
                    v_isShared_1609_ = v_isSharedCheck_1616_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1610_ = l_Lean_Linter_getLinterValueExtra(v_linterOption_1599_, v_a_1606_);
                lean_dec(v_a_1606_);
                if v___x_1610_ == 0 {
                    lean_dec_ref(v_msg_1601_);
                    lean_dec_ref(v_linterOption_1599_);
                    v___x_1611_ = lean_box(0);
                    if v_isShared_1609_ == 0 {
                        lean_ctor_set(v___x_1608_, 0, v___x_1611_);
                        v___x_1613_ = v___x_1608_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
                        v___x_1613_ = v_reuseFailAlloc_1614_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1608_);
                    v___x_1615_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_linterOption_1599_, v_stx_1600_, v_msg_1601_, v___y_1602_, v___y_1603_);
                    return v___x_1615_;
                }
            }
            2 => {
                return v___x_1613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(
    mut v_linterOption_1617_: *mut LeanObject,
    mut v_stx_1618_: *mut LeanObject,
    mut v_msg_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1623_: *mut LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_linterOption_1617_, v_stx_1618_, v_msg_1619_, v___y_1620_, v___y_1621_);
    lean_dec(v___y_1621_);
    lean_dec_ref(v___y_1620_);
    lean_dec(v_stx_1618_);
    return v_res_1623_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2;
    v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5()
-> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4;
    v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(
    mut v_as_1633_: *mut LeanObject,
    mut v_sz_1634_: usize,
    mut v_i_1635_: usize,
    mut v_b_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_unused_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1645_ = lean_usize_dec_lt(v_i_1635_, v_sz_1634_);
                if v___x_1645_ == 0 {
                    v___x_1646_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1646_, 0, v_b_1636_);
                    return v___x_1646_;
                } else {
                    v___x_1647_ = lean_box(0);
                    v_a_1648_ = lean_array_uget_borrowed(v_as_1633_, v_i_1635_);
                    v___x_1649_ = l_Lean_Syntax_getId(v_a_1648_);
                    v___x_1650_ = l_Lean_Name_hasMacroScopes(v___x_1649_);
                    if v___x_1650_ == 0 {
                        v___x_1651_ = l_Lean_isPrivateName(v___x_1649_);
                        if v___x_1651_ == 0 {
                            v___x_1652_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
                            lean_inc(v___x_1649_);
                            v___x_1653_ = l_Lean_Name_components(v___x_1649_);
                            if lean_obj_tag(v___x_1653_) == 0 {
                                v___y_1655_ = v___x_1653_;
                                state = 2;
                                continue;
                            } else {
                                v_tail_1677_ = lean_ctor_get(v___x_1653_, 1);
                                lean_inc(v_tail_1677_);
                                v___y_1655_ = v_tail_1677_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1649_);
                            v_a_1641_ = v___x_1647_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1649_);
                        v_a_1641_ = v___x_1647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1642_ = 1usize;
                v___x_1643_ = lean_usize_add(v_i_1635_, v___x_1642_);
                v_i_1635_ = v___x_1643_;
                v_b_1636_ = v_a_1641_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1656_ = l_List_zipWith___at___00List_zip_spec__0(
                    lean_box(0),
                    lean_box(0),
                    v___x_1653_,
                    v___y_1655_,
                );
                v___x_1657_ = l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v___x_1656_);
                lean_dec(v___x_1656_);
                if lean_obj_tag(v___x_1657_) == 1 {
                    v_val_1658_ = lean_ctor_get(v___x_1657_, 0);
                    lean_inc(v_val_1658_);
                    lean_dec_ref_known(v___x_1657_, 1);
                    v_fst_1659_ = lean_ctor_get(v_val_1658_, 0);
                    v_isSharedCheck_1675_ = (!lean_is_exclusive(v_val_1658_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v_unused_1676_ = lean_ctor_get(v_val_1658_, 1);
                        lean_dec(v_unused_1676_);
                        v___x_1661_ = v_val_1658_;
                        v_isShared_1662_ = v_isSharedCheck_1675_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_fst_1659_);
                        lean_dec(v_val_1658_);
                        v___x_1661_ = lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1675_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1657_);
                    lean_dec(v___x_1649_);
                    v_a_1641_ = v___x_1647_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1663_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
                v___x_1664_ = l_Lean_MessageData_ofName(v_fst_1659_);
                if v_isShared_1662_ == 0 {
                    lean_ctor_set_tag(v___x_1661_, 7);
                    lean_ctor_set(v___x_1661_, 1, v___x_1664_);
                    lean_ctor_set(v___x_1661_, 0, v___x_1663_);
                    v___x_1666_ = v___x_1661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1674_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1663_);
                    lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1664_);
                    v___x_1666_ = v_reuseFailAlloc_1674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1667_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3);
                v___x_1668_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1668_, 0, v___x_1666_);
                lean_ctor_set(v___x_1668_, 1, v___x_1667_);
                v___x_1669_ = l_Lean_MessageData_ofName(v___x_1649_);
                v___x_1670_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1670_, 0, v___x_1668_);
                lean_ctor_set(v___x_1670_, 1, v___x_1669_);
                v___x_1671_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5);
                v___x_1672_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1672_, 0, v___x_1670_);
                lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_1652_, v_a_1648_, v___x_1672_, v___y_1637_, v___y_1638_);
                if lean_obj_tag(v___x_1673_) == 0 {
                    lean_dec_ref_known(v___x_1673_, 1);
                    v_a_1641_ = v___x_1647_;
                    state = 1;
                    continue;
                } else {
                    return v___x_1673_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(
    mut v_as_1678_: *mut LeanObject,
    mut v_sz_1679_: *mut LeanObject,
    mut v_i_1680_: *mut LeanObject,
    mut v_b_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1685_: usize = 0;
    let mut v_i_boxed_1686_: usize = 0;
    let mut v_res_1687_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1679_);
    lean_dec(v_sz_1679_);
    v_i_boxed_1686_ = lean_unbox_usize(v_i_1680_);
    lean_dec(v_i_1680_);
    v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v_as_1678_, v_sz_boxed_1685_, v_i_boxed_1686_, v_b_1681_, v___y_1682_, v___y_1683_);
    lean_dec(v___y_1683_);
    lean_dec_ref(v___y_1682_);
    lean_dec_ref(v_as_1678_);
    return v_res_1687_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(
    mut v___x_1688_: u8,
    mut v___x_1689_: *mut LeanObject,
    mut v_as_1690_: *mut LeanObject,
    mut v_sz_1691_: usize,
    mut v_i_1692_: usize,
    mut v_b_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: u8 = 0;
    let mut v___y_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: usize = 0;
    let mut v___x_1707_: usize = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1695_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
                if v___x_1695_ == 0 {
                    lean_dec(v___x_1689_);
                    v___x_1696_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1696_, 0, v_b_1693_);
                    return v___x_1696_;
                } else {
                    v_a_1697_ = lean_array_uget_borrowed(v_as_1690_, v_i_1692_);
                    v___x_1698_ = l_Lean_TSyntax_getId(v_a_1697_);
                    v___x_1699_ = 0;
                    v___x_1709_ = l_Lean_Syntax_getRange_x3f(v_a_1697_, v___x_1699_);
                    if lean_obj_tag(v___x_1709_) == 0 {
                        v___x_1710_ = l_Lean_Syntax_instInhabitedRange_default;
                        v___y_1701_ = v___x_1710_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1711_ = lean_ctor_get(v___x_1709_, 0);
                        lean_inc(v_val_1711_);
                        lean_dec_ref_known(v___x_1709_, 1);
                        v___y_1701_ = v_val_1711_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1702_ = l_Lean_Syntax_ofRange(v___y_1701_, v___x_1688_);
                lean_inc(v___x_1689_);
                v___x_1703_ = l_Lean_Name_append(v___x_1689_, v___x_1698_);
                v___x_1704_ = l_Lean_mkIdentFrom(v___x_1702_, v___x_1703_, v___x_1699_);
                lean_dec(v___x_1702_);
                v___x_1705_ = lean_array_push(v_b_1693_, v___x_1704_);
                v___x_1706_ = 1usize;
                v___x_1707_ = lean_usize_add(v_i_1692_, v___x_1706_);
                v_i_1692_ = v___x_1707_;
                v_b_1693_ = v___x_1705_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg___boxed(
    mut v___x_1712_: *mut LeanObject,
    mut v___x_1713_: *mut LeanObject,
    mut v_as_1714_: *mut LeanObject,
    mut v_sz_1715_: *mut LeanObject,
    mut v_i_1716_: *mut LeanObject,
    mut v_b_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7599__boxed_1719_: u8 = 0;
    let mut v_sz_boxed_1720_: usize = 0;
    let mut v_i_boxed_1721_: usize = 0;
    let mut v_res_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_7599__boxed_1719_ = (lean_unbox(v___x_1712_) as u8);
    v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1715_);
    lean_dec(v_sz_1715_);
    v_i_boxed_1721_ = lean_unbox_usize(v_i_1716_);
    lean_dec(v_i_1716_);
    v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_7599__boxed_1719_, v___x_1713_, v_as_1714_, v_sz_boxed_1720_, v_i_boxed_1721_, v_b_1717_);
    lean_dec_ref(v_as_1714_);
    return v_res_1722_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(
    mut v_stx_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_aliases_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1737_: usize = 0;
    let mut v___x_1738_: usize = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aliases_1727_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0;
                v___x_1728_ =
                    l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3;
                lean_inc(v_stx_1723_);
                v___x_1729_ = l_Lean_Syntax_isOfKind(v_stx_1723_, v___x_1728_);
                if v___x_1729_ == 0 {
                    lean_dec(v_stx_1723_);
                    v___x_1730_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1730_, 0, v_aliases_1727_);
                    return v___x_1730_;
                } else {
                    v___x_1731_ = l_Lean_Elab_Command_getScope___redArg(v___y_1725_);
                    if lean_obj_tag(v___x_1731_) == 0 {
                        v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
                        lean_inc(v_a_1732_);
                        lean_dec_ref_known(v___x_1731_, 1);
                        v_currNamespace_1733_ = lean_ctor_get(v_a_1732_, 2);
                        lean_inc(v_currNamespace_1733_);
                        lean_dec(v_a_1732_);
                        v___x_1734_ = lean_unsigned_to_nat(3);
                        v___x_1735_ = l_Lean_Syntax_getArg(v_stx_1723_, v___x_1734_);
                        lean_dec(v_stx_1723_);
                        v_ids_1736_ = l_Lean_Syntax_getArgs(v___x_1735_);
                        lean_dec(v___x_1735_);
                        v_sz_1737_ = lean_array_size(v_ids_1736_);
                        v___x_1738_ = 0usize;
                        v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_1729_, v_currNamespace_1733_, v_ids_1736_, v_sz_1737_, v___x_1738_, v_aliases_1727_);
                        lean_dec_ref(v_ids_1736_);
                        if lean_obj_tag(v___x_1739_) == 0 {
                            v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
                            v_isSharedCheck_1747_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                            if v_isSharedCheck_1747_ == 0 {
                                v___x_1742_ = v___x_1739_;
                                v_isShared_1743_ = v_isSharedCheck_1747_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1740_);
                                lean_dec(v___x_1739_);
                                v___x_1742_ = lean_box(0);
                                v_isShared_1743_ = v_isSharedCheck_1747_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
                            v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                            if v_isSharedCheck_1755_ == 0 {
                                v___x_1750_ = v___x_1739_;
                                v_isShared_1751_ = v_isSharedCheck_1755_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1748_);
                                lean_dec(v___x_1739_);
                                v___x_1750_ = lean_box(0);
                                v_isShared_1751_ = v_isSharedCheck_1755_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_stx_1723_);
                        v_a_1756_ = lean_ctor_get(v___x_1731_, 0);
                        v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1731_)) as u8;
                        if v_isSharedCheck_1763_ == 0 {
                            v___x_1758_ = v___x_1731_;
                            v_isShared_1759_ = v_isSharedCheck_1763_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1756_);
                            lean_dec(v___x_1731_);
                            v___x_1758_ = lean_box(0);
                            v_isShared_1759_ = v_isSharedCheck_1763_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1743_ == 0 {
                    v___x_1745_ = v___x_1742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1745_;
            }
            3 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1753_;
            }
            5 => {
                if v_isShared_1759_ == 0 {
                    v___x_1761_ = v___x_1758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
                    v___x_1761_ = v_reuseFailAlloc_1762_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___boxed(
    mut v_stx_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1768_: *mut LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v_stx_1764_, v___y_1765_, v___y_1766_);
    lean_dec(v___y_1766_);
    lean_dec_ref(v___y_1765_);
    return v_res_1768_;
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(
    mut v___f_1769_: *mut LeanObject,
    mut v_stx_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1783_: usize = 0;
    let mut v___x_1784_: usize = 0;
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_unused_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_aliases_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1810_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_1771_, v___y_1772_);
                v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
                v_isSharedCheck_1834_ = (!lean_is_exclusive(v___x_1810_)) as u8;
                if v_isSharedCheck_1834_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    v_isShared_1814_ = v_isSharedCheck_1834_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_a_1811_);
                    lean_dec(v___x_1810_);
                    v___x_1813_ = lean_box(0);
                    v_isShared_1814_ = v_isSharedCheck_1834_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_1779_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v___y_1778_, v___y_1777_, v___y_1776_);
                lean_dec(v___y_1778_);
                if lean_obj_tag(v___x_1779_) == 0 {
                    v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
                    lean_inc(v_a_1780_);
                    lean_dec_ref_known(v___x_1779_, 1);
                    v___x_1781_ = l_Array_append___redArg(v_a_1780_, v___y_1775_);
                    lean_dec_ref(v___y_1775_);
                    v___x_1782_ = lean_box(0);
                    v_sz_1783_ = lean_array_size(v___x_1781_);
                    v___x_1784_ = 0usize;
                    v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_1781_, v_sz_1783_, v___x_1784_, v___x_1782_, v___y_1777_, v___y_1776_);
                    lean_dec_ref(v___x_1781_);
                    if lean_obj_tag(v___x_1785_) == 0 {
                        v_isSharedCheck_1792_ = (!lean_is_exclusive(v___x_1785_)) as u8;
                        if v_isSharedCheck_1792_ == 0 {
                            v_unused_1793_ = lean_ctor_get(v___x_1785_, 0);
                            lean_dec(v_unused_1793_);
                            v___x_1787_ = v___x_1785_;
                            v_isShared_1788_ = v_isSharedCheck_1792_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1785_);
                            v___x_1787_ = lean_box(0);
                            v_isShared_1788_ = v_isSharedCheck_1792_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1785_;
                    }
                } else {
                    lean_dec_ref(v___y_1775_);
                    v_a_1794_ = lean_ctor_get(v___x_1779_, 0);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1779_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1779_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1794_);
                        lean_dec(v___x_1779_);
                        v___x_1796_ = lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1788_ == 0 {
                    lean_ctor_set(v___x_1787_, 0, v___x_1782_);
                    v___x_1790_ = v___x_1787_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1782_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1790_;
            }
            4 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1799_;
            }
            6 => {
                v___x_1806_ = 0;
                v___x_1807_ = l_Lean_Syntax_getPos_x3f(v_stx_1770_, v___x_1806_);
                lean_dec(v_stx_1770_);
                if lean_obj_tag(v___x_1807_) == 0 {
                    v___x_1808_ = lean_unsigned_to_nat(0);
                    v___y_1775_ = v_aliases_1803_;
                    v___y_1776_ = v___y_1805_;
                    v___y_1777_ = v___y_1804_;
                    v___y_1778_ = v___x_1808_;
                    state = 1;
                    continue;
                } else {
                    v_val_1809_ = lean_ctor_get(v___x_1807_, 0);
                    lean_inc(v_val_1809_);
                    lean_dec_ref_known(v___x_1807_, 1);
                    v___y_1775_ = v_aliases_1803_;
                    v___y_1776_ = v___y_1805_;
                    v___y_1777_ = v___y_1804_;
                    v___y_1778_ = v_val_1809_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_1815_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
                v___x_1816_ = l_Lean_Linter_getLinterValueExtra(v___x_1815_, v_a_1811_);
                lean_dec(v_a_1811_);
                if v___x_1816_ == 0 {
                    lean_dec(v_stx_1770_);
                    lean_dec_ref(v___f_1769_);
                    v___x_1817_ = lean_box(0);
                    if v_isShared_1814_ == 0 {
                        lean_ctor_set(v___x_1813_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1813_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1813_);
                    lean_inc(v_stx_1770_);
                    v___x_1821_ = l_Lean_Syntax_find_x3f(v_stx_1770_, v___f_1769_);
                    if lean_obj_tag(v___x_1821_) == 1 {
                        v_val_1822_ = lean_ctor_get(v___x_1821_, 0);
                        lean_inc(v_val_1822_);
                        lean_dec_ref_known(v___x_1821_, 1);
                        v___x_1823_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v_val_1822_, v___y_1771_, v___y_1772_);
                        if lean_obj_tag(v___x_1823_) == 0 {
                            v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
                            lean_inc(v_a_1824_);
                            lean_dec_ref_known(v___x_1823_, 1);
                            v_aliases_1803_ = v_a_1824_;
                            v___y_1804_ = v___y_1771_;
                            v___y_1805_ = v___y_1772_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_stx_1770_);
                            v_a_1825_ = lean_ctor_get(v___x_1823_, 0);
                            v_isSharedCheck_1832_ = (!lean_is_exclusive(v___x_1823_)) as u8;
                            if v_isSharedCheck_1832_ == 0 {
                                v___x_1827_ = v___x_1823_;
                                v_isShared_1828_ = v_isSharedCheck_1832_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1825_);
                                lean_dec(v___x_1823_);
                                v___x_1827_ = lean_box(0);
                                v_isShared_1828_ = v_isSharedCheck_1832_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1821_);
                        v___x_1833_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0;
                        v_aliases_1803_ = v___x_1833_;
                        v___y_1804_ = v___y_1771_;
                        v___y_1805_ = v___y_1772_;
                        state = 6;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_1819_;
            }
            9 => {
                if v_isShared_1828_ == 0 {
                    v___x_1830_ = v___x_1827_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(
    mut v___f_1835_: *mut LeanObject,
    mut v_stx_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1840_: *mut LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(
        v___f_1835_,
        v_stx_1836_,
        v___y_1837_,
        v___y_1838_,
    );
    lean_dec(v___y_1838_);
    lean_dec_ref(v___y_1837_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(
    mut v_o_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_1857_, v___y_1859_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(
    mut v_o_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(v_o_1862_, v___y_1863_, v___y_1864_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    return v_res_1866_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(
    mut v___x_1867_: *mut LeanObject,
    mut v_pos_1868_: *mut LeanObject,
    mut v_init_1869_: *mut LeanObject,
    mut v_x_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1867_, v_pos_1868_, v_init_1869_, v_x_1870_);
    return v___x_1874_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(
    mut v___x_1875_: *mut LeanObject,
    mut v_pos_1876_: *mut LeanObject,
    mut v_init_1877_: *mut LeanObject,
    mut v_x_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_res_1882_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(v___x_1875_, v_pos_1876_, v_init_1877_, v_x_1878_, v___y_1879_, v___y_1880_);
    lean_dec(v___y_1880_);
    lean_dec_ref(v___y_1879_);
    lean_dec(v_pos_1876_);
    lean_dec_ref(v___x_1875_);
    return v_res_1882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8(
    mut v___x_1883_: u8,
    mut v___x_1884_: *mut LeanObject,
    mut v_as_1885_: *mut LeanObject,
    mut v_sz_1886_: usize,
    mut v_i_1887_: usize,
    mut v_b_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_1883_, v___x_1884_, v_as_1885_, v_sz_1886_, v_i_1887_, v_b_1888_);
    return v___x_1892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___boxed(
    mut v___x_1893_: *mut LeanObject,
    mut v___x_1894_: *mut LeanObject,
    mut v_as_1895_: *mut LeanObject,
    mut v_sz_1896_: *mut LeanObject,
    mut v_i_1897_: *mut LeanObject,
    mut v_b_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7945__boxed_1902_: u8 = 0;
    let mut v_sz_boxed_1903_: usize = 0;
    let mut v_i_boxed_1904_: usize = 0;
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v___x_7945__boxed_1902_ = (lean_unbox(v___x_1893_) as u8);
    v_sz_boxed_1903_ = lean_unbox_usize(v_sz_1896_);
    lean_dec(v_sz_1896_);
    v_i_boxed_1904_ = lean_unbox_usize(v_i_1897_);
    lean_dec(v_i_1897_);
    v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8(v___x_7945__boxed_1902_, v___x_1894_, v_as_1895_, v_sz_boxed_1903_, v_i_boxed_1904_, v_b_1898_, v___y_1899_, v___y_1900_);
    lean_dec(v___y_1900_);
    lean_dec_ref(v___y_1899_);
    lean_dec_ref(v_as_1895_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11(
    mut v_msgData_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v_msgData_1906_, v___y_1908_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___boxed(
    mut v_msgData_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11(v_msgData_1911_, v___y_1912_, v___y_1913_);
    lean_dec(v___y_1913_);
    lean_dec_ref(v___y_1912_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace;
    v___x_1918_ = l_Lean_Elab_Command_addLinter(v___x_1917_);
    return v___x_1918_;
}
pub unsafe fn l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(
    mut v_a_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
    return v_res_1920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Extra_DupNamespace(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_linter_extra_dupNamespace = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_dupNamespace);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Extra_DupNamespace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Extra_DupNamespace(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Linter_Extra_DupNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Extra_DupNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Extra_DupNamespace(builtin);
}
